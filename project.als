sig Track {
	succs : set Track,
    var state: one State,
}
sig Entry, Exit in Track {}

abstract sig State {}
one sig Free, Occupied, Unknown extends State {}

fun FreeTrack: set Track {
    state.Free
}
fun OccupiedTrack: set Track {
    state.Occupied
}
fun UnknownTrack: set Track {
    state.Unknown
}

fact trackInit {
    // No loops
    disj[iden, ^succs]

    // Entries are the tracks that have no predecessors
	Entry = (Track - Track.succs)
    // Exits are the tracks that have no successors
	Exit = (Track - succs.Track)

    // All exits accessible from all entries
    all e: Entry | Exit in e.^succs

    // At the start all tracks are free
    Track = FreeTrack
}

sig Train {
    var track: lone Track,
    var lastKnownHeadTrack: lone Track,
    var lastKnownTailTrack: lone Track,
}
var sig Offline, Split in Train {}

fact trainInit {
    // At the start trains are not in any track
    no track
    no lastKnownHeadTrack
    no lastKnownTailTrack

    // At the start trains are not split or offline
    no Split
    no Offline
}

// Events

pred enter[train: Train, entry: Entry] {
    // Guard: the train is not in any track
    no train.track
    
    // Guard: the entry is free
    entry in FreeTrack

    // Effect: the train enters the track
    track' = track ++ train -> entry
    lastKnownHeadTrack' = lastKnownHeadTrack ++ train -> entry
    lastKnownTailTrack' = lastKnownTailTrack ++ train -> entry

    // Frame conditions
    Offline' = Offline
    Split' = Split
}

pred exit[train: Train] {
    // Guard: the train is not split or offline
    train not in Split
    train not in Offline

    // Guard: the train is in an exit
    some train.track
    train.track in Exit

    // Effect: the train exits the track
    track' = track - (train -> Track)
    lastKnownHeadTrack' = lastKnownHeadTrack - (train -> Track)
    lastKnownTailTrack' = lastKnownTailTrack - (train -> Track)

    // Frame conditions
    Offline' = Offline
    Split' = Split
}

pred move[train: Train] {
    // Guard: the train is in a track
    some train.track

    // Guard: the train cannot move onto a track that is not free
    train.track' in FreeTrack

    // Effect: the train moves to the next track
    one train.track'
    track' in track + (train <: track.succs)
    track - (train -> Track) in track'

    // Effect: the train updates its position
    updateTrainPosition[train]

    // Frame conditions
    Offline' = Offline
    Split' = Split
}

pred split[train: Train] {
    // Guard: the train is in a track
    some train.track

    // Guard: the train is not split
    train not in Split 

    // Effect: the train is split
    Split' = Split + train    

    // Frame conditions
    track' = track
    lastKnownHeadTrack' = lastKnownHeadTrack
    lastKnownTailTrack' = lastKnownTailTrack
    Offline' = Offline
}

pred disconnect[train: Train] {
    // Guard: the train is in a track
    some train.track

    // Guard: the train is online
    train not in Offline

    // Effect: the train disconnects
    Offline' = Offline + train

    // Frame conditions
    track' = track
    lastKnownHeadTrack' = lastKnownHeadTrack
    lastKnownTailTrack' = lastKnownTailTrack
    Split' = Split
}

pred connect[train: Train] {
    // Guard: the train is in a track
    some train.track

    // Guard: the train is offline
    train in Offline

    // Effect: the train reconnects
    Offline' = Offline - train

    // Effect: the train updates its position
    updateTrainPosition[train]

    // Frame conditions
    track' = track
    Split' = Split
}

pred stutter {
    track' = track
    lastKnownHeadTrack' = lastKnownHeadTrack
    lastKnownTailTrack' = lastKnownTailTrack
    Offline' = Offline
    Split' = Split
}

pred updateTrainPosition[train: Train] {
    // if online, the train updates its position
    train not in Offline' => (
        lastKnownHeadTrack' = lastKnownHeadTrack ++ train <: track' &&
        // if not split, the tail position is updated
        (train not in Split' => lastKnownTailTrack' = lastKnownTailTrack ++ train <: track'
        else lastKnownTailTrack' = lastKnownTailTrack)
    ) else (
        lastKnownHeadTrack' = lastKnownHeadTrack &&
        lastKnownTailTrack' = lastKnownTailTrack
    )
}

pred updateTrackState {
    // if offline, the track is unknown from the tail forward
    // if split, the track is unknown from the tail to the head
    // if online, the track is occupied in the head
    all track: Track | (
        (track in (Train - Offline).lastKnownHeadTrack) => track in OccupiedTrack else
        (track in Offline.lastKnownTailTrack.*succs) => track in UnknownTrack else
        (some t: Split - Offline | track in (t.lastKnownTailTrack.*succs & t.lastKnownHeadTrack.^~succs)) => track in UnknownTrack else
        track in FreeTrack
    )
}

fact transitions {
    always ((
        some train: Train, entry: Entry | enter[train, entry] or
        some train: Train | exit[train] or
        some train: Train | move[train] or
        some train: Train | split[train] or
        some train: Train | disconnect[train] or
        some train: Train | connect[train] or
        stutter
    ) and updateTrackState)
}

// Example scenarios

pred noForks {
    succs in Track lone -> lone Track
}

pred forks {
    some t: Track | not lone t.succs
}

pred noSplits {
    always no Split
}

pred splits {
    eventually some Split
}

pred noDisconnections {
    always no Offline
}

pred disconnections {
    eventually some Offline
}

pred eventuallyAllExit {
    all t: Train | eventually exit[t]
}

pred eventuallyAllAtOnce {
    eventually all t: Train | some t.track
}

// Only one train, no forks, no splits, no disconnections
run simplest {
    noForks
    noSplits
    noDisconnections
    eventuallyAllExit
} for 5 but exactly 1 Train, exactly 3 Track

// More trains, no forks, no splits, no disconnections
run lotsOfTrains {
    noForks
    noSplits
    noDisconnections
    eventuallyAllExit
    eventuallyAllAtOnce
} for 5 but exactly 3 Train, exactly 3 Track, 20 steps

// More trains, forks, splits, disconnections
run complicated {
    forks
    splits
    disconnections
    eventuallyAllAtOnce

    #Exit = 2
    #Entry = 2
} for 10 but exactly 3 Train, exactly 10 Track, 20 steps

// Temporal properties that should hold for every execution 

// A track that has a train car on it should be considered occupied or unknown
check trackWithTrainOccupiedOrUnknown {
    always Train.track in OccupiedTrack + UnknownTrack
}

// There should be no collisions (two trains in the same track)
check noCollisions {
    always all disj t1, t2: track.Track | t1.track != t2.track
}
