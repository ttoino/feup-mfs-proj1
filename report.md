# Formal Methods for Critical Systems - Alloy Project Report - Group 4

| Name                                      | UP        |
| ----------------------------------------- | --------- |
| Anete Medina Pereira                      | 202008856 |
| João António Semedo Pereira               | 202007145 |
| Miguel Lourenço Pregal de Mesquita Montes | 202007516 |

## 1. Introduction

In this project we explore the modeling, validation, and verification of a Level 3 train control center's software using Alloy, a formal specification language. Our aim is to create a simplified version of the European Train Control System (ETCS) and ensure its functionality. This involves structuring how trains and tracks interact, confirming their behaviors align with expectations, verifying the absence of errors and other essential tasks. By doing so, we aim to construct a reliable digital model of train operations, facilitating smooth and safe functioning.

## 2. Structural and behavioral design

### 2.1 Model definition

#### Track

- We defined the train line as a graph of `Track`s, each representing a portion of the line. Each `Track` knows which Tracks come after itself.
- This graph is a directed acyclic graph, meaning that there are no loops in the track. Additionally, a track cannot be skipped, meaning that if there is a sequence A &rarr; B &rarr; C, there cannot be a sequence A &rarr; C.
- `Track`s can be categorized as `Entry` or `Exit` tracks based on their connectivity to other tracks. If a `Track` is the start of the line, it is an `Entry`, if it is the end of the line, it is an `Exit`. A track cannot be both an `Entry` and an `Exit`.
- The state of each track can be `Free`, `Occupied`, or `Unknown`, which is determined by the presence of trains and communication status.
- Initialization: At the systems initial phase, all tracks are considered to be in the `Free` state. This represents the default condition where no trains are present, and the tracks are available for use.

#### Train

- The `Train` signature represents the the core entities within our system: the trains.
- Trains are defined by these attributes:
  - `track`: indicates the current track the train occupies;
  - `lastKnownHeadTrack`: represents the most recent track where the system knows the front of the train was located;
  - `lastKnownTailTrack`: indicates the most recent track where the system knows the rear of the train was located.
- Additionally, two state attributes characterize the train's status:
  - `Offline`: denotes that the train is currently disconnected from the system;
  - `Split`: indicates that the train is segmented into multiple parts.
- Initialization: Initially, trains are not associated with any track and are neither `Split` nor `Offline`.


- In the early stages of our project, we started with a more complex model where trains were represented by their head, tail, and potential middle cars. However, as we progressed, we faced challenges, particularly when dealing with scenarios where trains could split. Managing the state and movements of multiple cars became quite confusing, leading to a very much complicated code. So, we opted for a simplified approach in our final implementation where each train is represented as a single entity, with a head and tail, no longer including middle cars. This simplification not only made our code cleaner but also made it easier to model train behaviors, especially in cases involving train splitting.

### 2.2 Dynamic elements

The `Track`'s `state` can change dynamically, based on the reported position and status of the trains.

The `Train`'s `track` attribute is updated as the train moves along the track line.
The `lastKnownHeadTrack` and `lastKnownTailTrack` attributes are updated according to the `Train`'s status to track the train's historical positions.
This status can also change dynamically, as the trains lose or restore their connection, or are split into multiple parts.

### 2.3 Modeling of events

The system's behavior is modeled through a series of predicates that define the possible events that can occur in the system.
Only one of the below events can happen at a time, except for track state updates, which happen in every step of the trace.

#### Train entry and exit

Train entry is modeled through the `enter` predicate:

- Trains can only enter the system if they are not already in it;
- Trains enter the system at an `Entry` track.

Train exit is modeled through the `exit` predicate:

- Trains can only exit the system if they are already in it;
- Trains cannot exit the system if they are split or offline;
- Trains exit the system at an `Exit` track.

#### Train movement

Train movement is modeled through the `move` predicate:

- Trains can only move if they have entered the system;
- Trains move along the track line, transitioning from one track to one of it's successors;
- Trains can only move to `Free` tracks;
- Trains send their updated position to the system after moving, unless they are `Offline`.
- If a train is split, it only updates the position of it's head.

#### Train splitting

Train splitting is modeled through the `split` predicate:

- Trains can only be split if they have entered the system and are not already split.

#### Train connection and disconnection

Train connection and disconnection are modeled through the `connect` and `disconnect` predicates:

- Trains can only be connected if they are offline;
- Trains can only be disconnected if they are not already offline.

#### Track state update

Track state update is modeled through the `updateTrackState` predicate:

- If a train is online, the track its head occupies is marked as `Occupied`;
- If a train is split, the track its head occupies is marked as `Occupied`, and the tracks between the head and tail are marked as `Unknown`;
- If a train is offline, the tracks ahead of itself are marked as `Unknown`;
- All other tracks are marked as `Free`.

### 2.4 Validation of structural and behavioral model

We employed run commands to explore and validate the expected configurations of our structural model.
The structural properties where checked in the first step of each trace, and the behavioral properties in the remaining steps.

The following run commands were utilized:

- `simplest`: A simple configuration with one train and three tracks, ensuring no forks, splits, or disconnections, and that the train eventually exits the system.
- `lotsOfTrains`: A more complex configuration with three trains and three tracks, ensuring no forks, splits, or disconnections, and that all trains are in the system at once and eventually exit the system.
- `complicated`: A complex configuration with three trains and ten tracks, ensuring forks, splits and disconnections, that the first train to enter is split at the entrance and then moves to an exit, that at least one train successfully exits, and that at the end there is a dead lock (no train can move).

### 2.5 Specification and Verification of structural properties

We employed check commands to verify the expected structure of our model.

The following check commands were utilized:

- `allExitsReachable`: A check to ensure that all `Exit` tracks are reachable from an `Entry` track.
- `someExitReachable`: A check to ensure that at least one `Exit` track is reachable from any track.

### 2.6 Specification and Verification of behavioral properties

We employed check commands to verify the expected behavior of our model.

The following check commands were utilized:

- `trackWithTrackOccupiedOrUnknown`: A check to ensure that tracks with a train on them are considered occupied or unknown.
- `noCollisions`: A check to ensure that there are no collisions, i.e., two trains in the same track.
- `noSplitsOrDisconnectionsAllCanExit`: A check to ensure that when there are no splits or disconnections, all trains can exit the system (but they don't have to).
- `noSplitsWithReconnectionsAllCanExit`: A check to ensure that when there are no splits, all trains can exit the system (but they don't have to), on the condition that all trains that disconnect eventually reconnect.

## 3. Theme definition

To facilitate a better understanding and visualization of the model configurations, we defined a theme:

- Trains are represented by blue trapezoids:
  - if the train is offline, it turns gray;
  - if the train is split, it becomes a parallelogram instead.

- Tracks are represented by rectangles:
  - if the track is free, it is colored green;
  - if the track is occupied, it is colored red;
  - if the track is unknown, it is colored yellow;
  - if the track is an entry, it is represented by a house instead;
  - if the track is an exit, it is represented by an octagon instead.

## 4. Conclusion

In conclusion, this project exemplifies the utility of formal specification and verification techniques, using Alloy, to model a Level 3 train control center's software. Our structural model delineates clear properties, enabling the creation of a digital representation of train operations. Through run commands and check commands, we assess the system's behavior and verify crucial properties such as track occupancy and absence of collisions. Overall, this project emphasizes the efficacy of formal methods like Alloy in designing, validating, and verifying intricate systems like train control centers.
