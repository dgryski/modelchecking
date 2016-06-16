// Package river simulates farmer/wolf/goat/cabbage
package river

import (
	"errors"
	"log"

	"github.com/dgryski/modelchecking/go/runway"
)

type env struct {
	farmer  bool
	wolf    bool
	goat    bool
	cabbage bool
}

func NewEnv() *env {
	var e env
	return &e
}

func (env *env) Log() {
	log.Printf("farmer=%v wolf=%v goat=%v cabbage=%v\n", env.farmer, env.wolf, env.goat, env.cabbage)
}

func Invariants() []runway.Invariant {
	return []runway.Invariant{
		invariantCantCross,
	}
}

func invariantCantCross(ctx *runway.Context) error {
	env := ctx.Env.(*env)

	if !env.farmer || !env.wolf || !env.goat || !env.cabbage {
		return nil
	}

	return errors.New("assertion failed: !env.farmer || !env.wolf || !env.goat || !env.cabbage")
}

func crossFarmer(ctx *runway.Context, updateOK bool) (bool, error) {

	var changed bool
	env := ctx.Env.(*env)

	if env.wolf != env.goat && env.goat != env.cabbage {
		if !updateOK {
			return true, nil
		}
		changed = true
		env.farmer = !env.farmer
	}

	return changed, nil
}

func crossWolf(ctx *runway.Context, updateOK bool) (bool, error) {
	var changed bool
	env := ctx.Env.(*env)

	if env.farmer == env.wolf && env.goat != env.cabbage {
		if !updateOK {
			return true, nil
		}
		changed = true
		env.farmer = !env.farmer
		env.wolf = !env.wolf
	}

	return changed, nil
}

func crossGoat(ctx *runway.Context, updateOK bool) (bool, error) {
	var changed bool
	env := ctx.Env.(*env)

	if env.farmer == env.goat {
		if !updateOK {
			return true, nil
		}
		changed = true
		env.farmer = !env.farmer
		env.goat = !env.goat
	}

	return changed, nil
}

func crossCabbage(ctx *runway.Context, updateOK bool) (bool, error) {
	var changed bool
	env := ctx.Env.(*env)

	if env.farmer == env.cabbage && env.wolf != env.goat {
		if !updateOK {
			return true, nil
		}
		changed = true
		env.farmer = !env.farmer
		env.cabbage = !env.cabbage
	}

	return changed, nil
}

func Rules() []runway.Rule {
	return []runway.Rule{
		{Fire: crossFarmer, Name: "crossFarmer"},
		{Fire: crossWolf, Name: "crossWolf"},
		{Fire: crossGoat, Name: "crossGoat"},
		{Fire: crossCabbage, Name: "crossCabbage"},
	}
}
