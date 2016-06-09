// Command banana simulates Too Many Bananas
package main

import (
	"flag"
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

func bananaRangeCheck(ctx *context) {
	if ctx.env.bananas >= 0 && ctx.env.bananas <= 100 {
		return
	}
	ctx.assertFailed("bananas out of range: 0..100")
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

func invariantBananaLimit(ctx *context) {
	if ctx.env.bananas <= 8 {
		return
	}

	ctx.assertFailed("bananas <= 8")
}

func ruleStep(ctx *context, i int) {
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
			bananaRangeCheck(ctx)
			ctx.env.roommates[i].State = PersonHappy
		}
	case PersonGoingToStore:
		ctx.env.roommates[i].State = PersonReturningFromStore
		ctx.env.roommates[i].Carrying = int(ctx.rand.Intn(9)) // 0..8
	case PersonReturningFromStore:
		ctx.env.bananas += ctx.env.roommates[i].Carrying
		bananaRangeCheck(ctx)
		ctx.env.roommates[i].Carrying = 0
		ctx.env.notePresent = false
		ctx.env.roommates[i].State = PersonHungry
	}
}

var broken = flag.Bool("broken", false, "run broken algorithm")

func main() {
	verbose := flag.Bool("v", false, "verbose")

	flag.Parse()

	ctx := newContext()

	var rules []func(*context)

	for i := range ctx.env.roommates {
		i := i
		rules = append(rules, func(ctx *context) { ruleStep(ctx, i) })
	}

	for {
		r := rules[ctx.rand.Intn(uint64(len(rules)))]

		r(ctx)

		invariantBananaLimit(ctx)

		if *verbose {
			ctx.log()
		}
		ctx.clock++
	}
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
