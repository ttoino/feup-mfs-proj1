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
    var lastKnownTrack: one Track,
}
sig Tail in TrainCar {}
sig Head in TrainCar {
    var lastKnownTailPosition: one Track,
}
var sig Offline in Head {}

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

// Events

pred move[car: TrainCar] {
    // Guard: must not be split
    some Head & car.*succ

    // Guard: the successor must be ahead
    car.succ.track in car.track.^succs

    // Guard: if head, the next track must be free
    car in Head => car.track.succs.state = Free

    // Effect: the car moves to the next track
    track' = track ++ car <: track.succs

    // Effect: if head and online, send positions
    car in Head - Offline => updatePosition[car]

    // Effect: if tail is connected to head, update last known position of the tail
    some h: Head | car in Tail and h in car.^succ => h.lastKnownTailPosition' = car.track

    // Effect: if tail is connected and head is online, set the track free
    some h: Head | car in Tail and h in car.^succ and h not in Offline => car.track.state' = Free // Maybe change to a new predicate

    // Frame conditions
    Offline' = Offline
}
pred updatePosition[head: Head] {
    // Effect: the train updates its position
    lastKnownTrack' = lastKnownTrack ++ head.*~succ <: track

    // Effect: the tracks where the train is are marked as occupied
    state' = state ++ head.*~succ.lastKnownTrack -> Occupied

    // Effect: the tracks between the last known position of the tail and the last connected position of the train are marked as Unknown
    state' = state ++ (head.lastKnownTailPosition.*succs - head.*~succ.lastKnownTrack.*succs) -> Unknown

    // Frame conditions
    succ' = succ
    track' = track
    lastKnownTailPosition' = lastKnownTailPosition
    Offline' = Offline
}
pred split[car: TrainCar] {
    // Guard: the car is not the head of the train
    some car.succ

    // Effect: the car is disconnected from the train
    succ' = succ - (car <: succ)

    // Frame conditions
    state' = state
    track' = track
    lastKnownTrack' = lastKnownTrack
    lastKnownTailPosition' = lastKnownTailPosition
    Offline' = Offline
}
pred disconnect[head: Head] {
    // Guard: the head is online
    head not in Offline

    // Effect: the head loses connection
    Offline' = Offline + head

    // Effect: tracks are marked as unknown
    state' = state ++ head.*~succ.lastKnownTrack.*(succs :> Free) -> Unknown

    // Frame conditions
    state' = state
    succ' = succ
    track' = track
    lastKnownTrack' = lastKnownTrack
    lastKnownTailPosition' = lastKnownTailPosition
}
pred connect[head: Head] {
    // Guard: the head is offline
    head in Offline

    // Effect: the head reconnects
    Offline' = Offline - head

    // Frame conditions
    state' = state
    succ' = succ
    track' = track
    lastKnownTrack' = lastKnownTrack
    lastKnownTailPosition' = lastKnownTailPosition
}
pred stutter {
    state' = state
    succ' = succ
    track' = track
    lastKnownTrack' = lastKnownTrack
    lastKnownTailPosition' = lastKnownTailPosition
    Offline' = Offline
}


fact init {
    // There is no loss of connection
    all h: Head | h not in Offline

    // The state of all tracks is known
    all t:Track | t.state != Unknown

    // The tracks occupied by train cars are Occupied
    all c: TrainCar | c.track.state = Occupied

    // There are no loose train cars
    all t:Tail | some h:Head | h in t.^succ
}

fact transitions {
    always (
        some car: TrainCar | move[car] or
        some car: TrainCar | split[car] or
        some head: Head | disconnect[head] or
        some head: Head | connect[head] or
        stutter
    )
}

// Temporal properties that should hold for every execution 

// A track that has a train car on it should be considered occupied or unknown
pred trackWithCarOccupiedOrUnknown {
    always TrainCar.track.state in Occupied + Unknown
}

check trackWithCarOccupiedOrUnknown for 10
