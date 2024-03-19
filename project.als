sig Track {
	succs : set Track,
    var state: one State,
}
sig Junction, Entry, Exit in Track {}

abstract sig State {}
one sig Free, Occupied, Unknown extends State {}

fun Free: set Track {
    { t: Track | t.state = Free }
}
fun Occupied: set Track {
    { t: Track | t.state = Occupied }
}
fun Unknown: set Track {
    { t: Track | t.state = Unknown }
}

fact Tracks {
    // No loops
    disj[iden, ^succs]

    // Entries are the tracks that have no predecessors
	Entry = (Track - Track.succs)
    // Exits are the tracks that have no successors
	Exit = (Track - succs.Track)

    // Junctions are the tracks that have more than one predecessor
    Junction = { j: Track | some p1, p2: succs.j | p1 != p2 }
}

sig TrainCar {
    var succ: lone TrainCar,
    var track: one Track,
}
sig Head, Tail in TrainCar {}
var sig Offline in TrainCar {}

fact Trains {
    // Head of the train has no successor
    Head = { t: TrainCar | no t.succ }
    // Tail of the train has no predecessor
    Tail = { t: TrainCar | no succ.t }
    
    // No loops
    always disj[iden, ^succ]

    // TrainCars can only have one successor and predecessor
    always succ in TrainCar lone -> lone TrainCar
}

fact TrainsAndTracks {
    // Successive train cars are on successive tracks or on the same track
    always all t: TrainCar | t.succ.track in t.track + t.track.succs
}

run {
    some Track
    some TrainCar
    some succ
    some succs
} for 10


// Train positions - definition
sig TrainCarPosition {
    car: one Head,
    var tracks: some Track
}

fact TrainCarPositions {
    car in TrainCarPosition one -> one Head
}

// Events

pred move[car: TrainCar] {
    no car
}
pred updatePosition[head: Head] {
    // Guard: the head is online
    head not in Offline

    // Effect: the head of the train updates its position
    tracks' = tracks ++ car.head -> head.*~succ.track
    state' = state ++ car.head.tracks' -> Occupied

    // Frame conditions
    succ' = succ
    track' = track
    Offline' = Offline
}
pred disconnect[car: TrainCar] {
    // Guard: the car is not the head of the train
    some car.succ

    // Effect: the car is disconnected from the train
    succ' = succ - (car <: succ)

    // Frame conditions
    state' = state
    track' = track
    tracks' = tracks
    Offline' = Offline
}
pred stutter {
    state' = state
    succ' = succ
    track' = track
    tracks' = tracks
    Offline' = Offline
}

fact transitions {
    always (
        some car: TrainCar | move[car] or
        some head: Head | updatePosition[head] or
        some car: TrainCar | disconnect[car] or
        stutter
    )
}

// Temporal properties that should hold for every execution 

// A track that has a train car on it should be considered occupied or unknown
pred trackWithCarOccupiedOrUnknown {
    always TrainCar.track.state in Occupied + Unknown
}
