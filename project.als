sig Track {
	succs : set Track,
	// signals : set Signal
}
sig Junction, Entry, Exit in Track {}
var sig Free, Occupied, Unknown in Track {}

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

// sig Signal {}
// sig Semaphore, Speed extends Signal {}

sig TrainCar {
    var succ: lone TrainCar,
    track: one Track
}
sig Head, Tail in TrainCar {}

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

// Train movement 

// Temporal properties that should hold for every execution 

