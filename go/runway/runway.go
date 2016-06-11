// Package runways contains types and runtime helpers for runway models
package runway

import (
	"log"
)

type Environment interface {
	Log()
}

type Context struct {
	Clock int
	Rand  Rng

	Env Environment
}

func AssertFailed(ctx *Context, assert string) {
	log.Println("assertion failed: ", assert)
	ctx.Env.Log()
}

type Rule struct {
	Fire func(*Context, bool) (bool, error)
	Name string
}

type Invariant func(*Context) error

type Rng uint64

func (r *Rng) next() uint64 {
	x := *r
	x ^= x >> 12 // a
	x ^= x << 25 // b
	x ^= x >> 27 // c
	*r = x
	return uint64(x * 2685821657736338717)

}

// Bound returns a uniform integer 0..n-1
func (r *Rng) Intn(n uint64) uint64 {
	threshold := -n % n
	for {
		x := r.next()
		if x >= threshold {
			return x % n
		}
	}
}
