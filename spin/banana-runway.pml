/* too many bananas */
/* model more closely matching https://github.com/salesforce/runway-model-toomanybananas/blob/master/toomanybananas.model */

/* count of bananas in the house */
byte bananas = 2;

/* is there a note? */
bool note;

mtype = { hungry, happy, goingToStore, returningFromStore }

inline buyBananas() {
    if
    :: carryingBananas = 0
    :: carryingBananas = 1
    :: carryingBananas = 2
    :: carryingBananas = 3
    :: carryingBananas = 4
    :: carryingBananas = 5
    :: carryingBananas = 6
    :: carryingBananas = 7
    :: carryingBananas = 8
    fi
}

active [5] proctype person() {

    mtype state = happy

    byte carryingBananas;

    do
    :: if
        :: state == happy -> atomic {
                state = hungry;
            }
        :: state == hungry -> atomic {
                if
                :: bananas == 0 ->
                    if
                    :: note -> /* roommate at store, try again later */
                    :: else ->
                        note = true
                        state = goingToStore
                    fi
                :: else ->
                    bananas = bananas - 1
progress:           state = happy;
                fi
            }
        :: state == goingToStore -> atomic {
                buyBananas()
                state = returningFromStore;
            }
        :: state == returningFromStore -> atomic {
            bananas = bananas + carryingBananas;
            note = false;
            state = hungry;
            }
        fi
    od
}

never {
    do
    :: assert(bananas <= 8);
    od
}
