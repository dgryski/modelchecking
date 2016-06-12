// Package banana simulates Too Many Bananas
package banana

import (
	"errors"
	"flag"
	"fmt"
	"log"

	"github.com/dgryski/modelchecking/go/runway"
)

type env struct {
	bananas     int
	notePresent bool

	roommates [5]Person
}

func NewEnv() *env {
	var e env
	e.bananas = 2
	for i := range e.roommates {
		e.roommates[i] = newPerson()
	}

	return &e
}

func bananaRangeCheck(ctx *runway.Context) error {

	env := ctx.Env.(*env)

	if env.bananas >= 0 && env.bananas <= 100 {
		return nil
	}
	return errors.New("bananas out of range: 0..100")
}

func (env *env) Log() {
	log.Printf("bananas = %d\n", env.bananas)
	log.Printf("notePresent = %+v\n", env.notePresent)
	for i := range env.roommates {
		log.Printf("env.roommates[%d] = %+v\n", i, env.roommates[i])
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

func Invariants() []runway.Invariant {
	return []runway.Invariant{
		invariantBananaLimit,
	}
}

func invariantBananaLimit(ctx *runway.Context) error {
	env := ctx.Env.(*env)

	if env.bananas <= 8 {
		return nil
	}

	return errors.New("assertion failed: bananas <= 8")
}

func ruleStep(ctx *runway.Context, updateOK bool, i int) (bool, error) {

	env := ctx.Env.(*env)

	var changed bool
	switch env.roommates[i].State {
	case PersonHappy:
		if !updateOK {
			return true, nil
		}
		changed = true
		env.roommates[i].State = PersonHungry
	case PersonHungry:
		if env.bananas == 0 {
			if !*broken && env.notePresent {
				// roommate at store -- try again later
			} else {
				if !updateOK {
					return true, nil
				}
				changed = true
				env.notePresent = true
				env.roommates[i].State = PersonGoingToStore
			}
		} else {
			if !updateOK {
				return true, nil
			}
			changed = true
			env.bananas -= 1
			if err := bananaRangeCheck(ctx); err != nil {
				return changed, err
			}
			env.roommates[i].State = PersonHappy
		}
	case PersonGoingToStore:
		if !updateOK {
			return true, nil
		}
		changed = true
		env.roommates[i].State = PersonReturningFromStore
		env.roommates[i].Carrying = int(ctx.Rand.Intn(9)) // 0..8
	case PersonReturningFromStore:
		if !updateOK {
			return true, nil
		}
		changed = true
		env.bananas += env.roommates[i].Carrying
		if err := bananaRangeCheck(ctx); err != nil {
			return changed, err
		}
		env.roommates[i].Carrying = 0
		env.notePresent = false
		env.roommates[i].State = PersonHungry
	}

	return changed, nil
}

var broken = flag.Bool("broken", false, "run broken algorithm")

func Rules() []runway.Rule {
	var rules []runway.Rule
	var env env
	for i := range env.roommates {
		i := i
		rules = append(rules, runway.Rule{
			Fire: func(ctx *runway.Context, updateok bool) (bool, error) { return ruleStep(ctx, updateok, i) },
			Name: fmt.Sprintf("roommate[%d] step", i),
		})
	}

	return rules
}
