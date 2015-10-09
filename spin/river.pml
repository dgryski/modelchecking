

/* true if crossed */
bool goat;
bool cabbage;
bool wolf;
bool farmer;

inline cross(a, b) {
        a = !a
        b = !b
}

inline crossAlone(a) {
        a = !a
}

inline log() {
    printf("farmer:%d goat:%d cabbage:%d wolf:%d\n", farmer, goat, cabbage, wolf);
}

active proctype river() {
    do
    :: if
            :: farmer == goat -> log(); printf("farmer+goat\n"); cross(farmer, goat)
            :: farmer == wolf && (goat != cabbage) -> log(); printf("farmer+wolf\n"); cross(farmer, wolf)
            :: farmer == cabbage && (wolf != goat) -> log() printf("farmer+cabbage\n"); cross(farmer, cabbage)
            :: (wolf != goat && goat != cabbage) -> log(); printf("farmer\n"); crossAlone(farmer)
     fi
    od
}

never {
    do
    :: assert(!(goat && cabbage && wolf))
    od
}
