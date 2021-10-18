// Command runway runs simulations
package main

import (
	"flag"
	"log"
	"time"

	"github.com/dgryski/go-ddmin"

	"github.com/dgryski/modelchecking/go/banana"
	"github.com/dgryski/modelchecking/go/river"
	"github.com/dgryski/modelchecking/go/runway"
)

type model struct {
	invariants []runway.Invariant
	NewEnv     func() runway.Environment
	rules      []runway.Rule
}

func (m *model) checkInvariants(ctx *runway.Context) error {
	for _, f := range m.invariants {
		if err := f(ctx); err != nil {
			return err
		}
	}

	return nil
}

type transition struct {
	r    runway.Rule
	rand runway.Rng
}

func main() {
	verbose := flag.Bool("v", false, "verbose")

	modelType := flag.String("model", "", "model to run")
	seed := flag.Int("seed", 0, "use random seed (0 == time)")

	flag.Parse()

	ctx := &runway.Context{}
	if *seed != 0 {
		ctx.Rand = runway.Rng(*seed)
	} else {
		ctx.Rand = runway.Rng(uint64(time.Now().UnixNano()))
	}

	var m *model
	switch *modelType {
	case "banana":
		m = &model{
			invariants: banana.Invariants(),
			NewEnv:     func() runway.Environment { return banana.NewEnv() },
			rules:      banana.Rules(),
		}
	case "river":
		m = &model{
			invariants: river.Invariants(),
			NewEnv:     func() runway.Environment { return river.NewEnv() },
			rules:      river.Rules(),
		}
	}

	ctx.Env = m.NewEnv()
	rules := m.rules

	var transitions []transition

	var failure error
	for {

		var active []int
		for i, r := range rules {
			if ok, _ := r.Fire(ctx, false); ok {
				active = append(active, i)
			}
		}

		ridx := active[ctx.Rand.Intn(uint64(len(active)))]
		r := rules[ridx]

		transitions = append(transitions, transition{r, ctx.Rand})

		if _, failure = r.Fire(ctx, true); failure != nil {
			break
		}

		if failure = m.checkInvariants(ctx); failure != nil {
			break
		}

		if *verbose {
			ctx.Env.Log()
		}
		ctx.Clock++
	}

	log.Println("got terminating error:", failure)
	ctx.Env.Log()

	log.Println("minimizing...")
	b := minimize(m, transitions, failure)

	log.Printf("minimized test run shrunk %d -> %d\n", len(transitions), len(b))

	log.Println("minimal trace:")
	m.runTransitions(b, transitions, true)
}

func (m *model) runTransitions(data []byte, transitions []transition, verbose bool) error {

	var ctx runway.Context

	ctx.Env = m.NewEnv()

	for _, v := range data {
		t := transitions[v]
		ctx.Rand = t.rand
		if verbose {
			log.Println("fire ", t.r.Name)
		}
		if _, err := t.r.Fire(&ctx, true); err != nil {
			return err
		}

		if err := m.checkInvariants(&ctx); err != nil {
			return err
		}

		if verbose {
			ctx.Env.Log()
		}

		ctx.Clock++
	}

	return nil
}

func minimize(m *model, transitions []transition, errWant error) []byte {

	b := make([]byte, len(transitions))
	for i := range b {
		b[i] = byte(i)
	}

	return ddmin.Minimize(b, func(b []byte) ddmin.Result {
		err := m.runTransitions(b, transitions, false)
		if err == nil {
			return ddmin.Pass
		}
		if err.Error() == errWant.Error() {
			return ddmin.Fail
		}
		return ddmin.Unresolved
	})
}
