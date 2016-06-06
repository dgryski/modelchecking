// Command banana simulates Too Many Bananas
package main

import (
	"flag"
	"log"
	"math/rand"
	"os"
)

var bananas = 2
var notePresent bool

//go:generate stringer -type PersonState .

type PersonState int

const (
	PersonHappy PersonState = iota
	PersonHungry
	PersonGoingToStore
	PersonReturningFromStore
)

type Person struct {
	State PersonState

	// No State-local storage for any of the States, except..

	// ReturningFromStore
	Carrying int
}

var roommates [5]Person

func dumpState(steps int) {
	log.Printf("state at time = %+v\n", steps)
	log.Printf("bananas = %d\n", bananas)
	log.Printf("notePresent = %+v\n", notePresent)
	for i := range roommates {
		log.Printf("roommates[%d] = %+v\n", i, roommates[i])
	}
}

func invariantBananaLimit() {
	if bananas <= 8 {
		return
	}

	dumpState(steps)
	os.Exit(1)
}

var steps int

func main() {
	verbose := flag.Bool("v", false, "verbose")
	broken := flag.Bool("broken", false, "run broken algorithm")

	flag.Parse()

	for {
		i := rand.Intn(len(roommates)) // pick a person to move

		switch roommates[i].State {
		case PersonHappy:
			roommates[i].State = PersonHungry
		case PersonHungry:
			if bananas == 0 {
				if !*broken && notePresent {
					// roommate at store -- try again later
				} else {
					notePresent = true
					roommates[i].State = PersonGoingToStore
				}
			} else {
				bananas -= 1
				roommates[i].State = PersonHappy
			}
		case PersonGoingToStore:
			roommates[i].State = PersonReturningFromStore
			roommates[i].Carrying = rand.Intn(9) // 0..8
		case PersonReturningFromStore:
			bananas += roommates[i].Carrying
			roommates[i].Carrying = 0
			notePresent = false
			roommates[i].State = PersonHungry
		}
		invariantBananaLimit()
		steps++

		if *verbose {
			dumpState(steps)
		}

		if steps%102400 == 0 {
			log.Printf("steps = %+v\n", steps)
		}
	}
}
