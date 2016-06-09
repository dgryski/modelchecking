// Command banana simulates Too Many Bananas
package main

import (
	"errors"
	"flag"
	"github.com/dgryski/go-ddmin"
	"log"
	"os"
)

type context struct {
	clock int
	rand  rng

	env struct {
		bananas     int
		notePresent bool

		roommates [5]Person
	}
}

func newContext() *context {
	var c context
	c.rand = 0x123456789ABCDEF
	c.env.bananas = 2
	for i := range c.env.roommates {
		c.env.roommates[i] = newPerson()
	}

	return &c
}

func (ctx *context) assertFailed(s string) {
	log.Println("assertion failed: ", s)
	ctx.log()
	os.Exit(1)
}

func bananaRangeCheck(ctx *context) error {
	if ctx.env.bananas >= 0 && ctx.env.bananas <= 100 {
		return nil
	}
	return errors.New("bananas out of range: 0..100")
}

func (ctx *context) log() {
	log.Printf("state at time = %+v\n", ctx.clock)
	log.Printf("bananas = %d\n", ctx.env.bananas)
	log.Printf("notePresent = %+v\n", ctx.env.notePresent)
	for i := range ctx.env.roommates {
		log.Printf("env.roommates[%d] = %+v\n", i, ctx.env.roommates[i])
	}
}

//go:generate stringer -type PersonState .

type PersonState int

const (
	PersonHappy PersonState = iota
	PersonHungry
	PersonGoingToStore
	PersonReturningFromStore
)

func newPerson() Person {
	var p Person
	return p
}

type Person struct {
	State PersonState

	// No State-local storage for any of the States, except..

	// ReturningFromStore
	Carrying int
}

var invariants = []func(*context) error{
	invariantBananaLimit,
}

func checkInvariants(ctx *context) error {

	for _, f := range invariants {
		if err := f(ctx); err != nil {
			return err
		}
	}

	return nil
}

func invariantBananaLimit(ctx *context) error {
	if ctx.env.bananas <= 8 {
		return nil
	}

	return errors.New("assertion failed: bananas <= 8")
}

func ruleStep(ctx *context, i int) error {
	switch ctx.env.roommates[i].State {
	case PersonHappy:
		ctx.env.roommates[i].State = PersonHungry
	case PersonHungry:
		if ctx.env.bananas == 0 {
			if !*broken && ctx.env.notePresent {
				// roommate at store -- try again later
			} else {
				ctx.env.notePresent = true
				ctx.env.roommates[i].State = PersonGoingToStore
			}
		} else {
			ctx.env.bananas -= 1
			if err := bananaRangeCheck(ctx); err != nil {
				return err
			}
			ctx.env.roommates[i].State = PersonHappy
		}
	case PersonGoingToStore:
		ctx.env.roommates[i].State = PersonReturningFromStore
		ctx.env.roommates[i].Carrying = int(ctx.rand.Intn(9)) // 0..8
	case PersonReturningFromStore:
		ctx.env.bananas += ctx.env.roommates[i].Carrying
		if err := bananaRangeCheck(ctx); err != nil {
			return err
		}
		ctx.env.roommates[i].Carrying = 0
		ctx.env.notePresent = false
		ctx.env.roommates[i].State = PersonHungry
	}

	return nil
}

var broken = flag.Bool("broken", false, "run broken algorithm")

type rule func(*context) error

type transition struct {
	r    rule
	rand rng
}

func main() {
	verbose := flag.Bool("v", false, "verbose")

	flag.Parse()

	ctx := newContext()

	var rules []rule

	for i := range ctx.env.roommates {
		i := i
		rules = append(rules, func(ctx *context) error { return ruleStep(ctx, i) })
	}

	var transitions []transition

	var failure error

	for {
		r := rules[ctx.rand.Intn(uint64(len(rules)))]

		transitions = append(transitions, transition{r, ctx.rand})

		if failure = r(ctx); failure != nil {
			break
		}

		if failure = checkInvariants(ctx); failure != nil {
			break
		}

		if *verbose {
			ctx.log()
		}
		ctx.clock++
	}

	log.Println("got terminating error:", failure)
	ctx.log()

	log.Println("minimizing...")
	b := minimize(transitions, failure)

	log.Printf("minimized test run shrunk %d -> %d\n", len(transitions), len(b))

	log.Println("minimal trace:")
	runTransitions(b, transitions, true)
}

func runTransitions(data []byte, transitions []transition, verbose bool) error {
	ctx := newContext()

	for _, v := range data {
		t := transitions[v]
		ctx.rand = t.rand
		if err := t.r(ctx); err != nil {
			return err
		}

		if err := checkInvariants(ctx); err != nil {
			return err
		}

		if verbose {
			ctx.log()
		}

		ctx.clock++
	}

	return nil
}

func minimize(transitions []transition, errWant error) []byte {

	b := make([]byte, len(transitions))
	for i := range b {
		b[i] = byte(i)
	}

	return ddmin.Minimize(b, func(b []byte) ddmin.Result {
		err := runTransitions(b, transitions, false)
		if err == nil {
			return ddmin.Pass
		}
		if err.Error() == errWant.Error() {
			return ddmin.Fail
		}
		return ddmin.Unresolved
	})
}

type rng uint64

func (r *rng) next() uint64 {
	x := *r
	x ^= x >> 12 // a
	x ^= x << 25 // b
	x ^= x >> 27 // c
	*r = x
	return uint64(x * 2685821657736338717)

}

// Bound returns a uniform integer 0..n-1
func (r *rng) Intn(n uint64) uint64 {
	threshold := -n % n
	for {
		x := r.next()
		if x >= threshold {
			return x % n
		}
	}
}
