## 1. Introduction
In this project we explore the modeling, validation, and verification of a Level 3 train control center's software using Alloy, a formal specification language. Our aim is to create a simplified version of the European Train Control System (ETCS) and ensure its functionality. This involves structuring how trains and tracks interact, confirming their behaviors align with expectations, verifying the absence of errors and other essential tasks. By doing so, we aim to construct a reliable digital model of train operations, facilitating smooth and safe functioning.


## 2. System structural design
### 2.1 Model definition
#### Track
- We defined the train line as a straight sequence of Tracks, each representing a portion of the line. Each Track know which Track comes after itself
- If a Track is the start of the line, it is an Entry, if it is the end of the line, it is an Exit and if it connects two lines, it is a Junction.


#### Train Car
- Each train is composed by a sequence of Train Cars, each knowing which Train Car is its own successor.
- The front of the train is the Head and has no successor. The back of the train is the Tail and isn't a successor of any other Train Car.

 
### 2.2 Validation of structural model
#### Run commands 
- We employed run commands to explore and validate the expected configurations of our structural model. The following run command was utilized: 
```als
run {
    some Track
    some TrainCar
    some succ
    some succs
} for 10
```

#### Themes definition
To facilitate a better understanding and visualization of the model configurations derived from our run commands, we defined specific themes:
- Node definitions: 
    - `Free, Int, Occupied, String, Track, univ, Unknown, seq/Int`: Define different types of nodes in the model.
    - `Entry, Exit, Head, Junction, Tail`: Define specific sets of nodes corresponding to certain roles or positions within the railway system. 
    - `TrainCar, TrainCarPosition`: Represent nodes related to train cars and their positions.
- Node appearance
    - **Color Black (Offline)**: Sets the color of nodes representing *Offline* train cars to black, making them visually distinguishable from other elements
    - **Color Red** and **Color Yellow**: Sets the color of nodes representing tracks in *Occupied* and *Unknown* states to red and yellow respectively, providing visual cues for track occupancy status.
    - **Color Green**: Colors nodes representing tracks in the *Free* state green, facilitating the identification of available track segments.
    - **Shape Parallelogram** and **Color Blue**: Assigns a parallelogram shape and a blue color to nodes representing train cars, aiding in their identification.
    - **Shape Trapezoid** and **Color Gray**: Specifies a trapezoid shape and a gray color for nodes representing train car positions, enhancing their visual representation. 
- Other Settings
    - **Visibile Attribute**: Controls the visibility of certain node types (e.g., State), ensuring they are not displayed in the graphical output when not relevant.

### 2.3 Specification and Verification of structural properties
- There are no loops in the Tracks and in the Train Cars. That means that a Track/Train Car cannot be within its successors.
- Entries/Tails have no successors.
- Exits/Heads have no predecessors (aren't successors of anything).
- Junctions have more than one predecessor.
- A Train Car can only have one successor and can only be the successor of one Train Car.
- Successive Train Cars are either on the same Track or on successive Tracks.

## 3. System behavioral design
### 3.1 Modelation of dynamic elements
- Each Train Car is in a specific position, in a Track.
- The system registers the last track where it knows the car was.
- The central system registers the state of each Track, being one of Free, Occupied or Unknown. If the state is Free, it means that the system is sure that there is no Train Car in that Track; if the state is Ocuupied, it means that the system is sure that there is at least one Train Car in that Track; if the state is Unknown, it means that the system can't be sure if there is or there isn't a Train Car in that Track. This could be because the train lost the connection to the system and could not update its position or because the train was split and some cars may have gotten loose.
- The Head of the train can be connected to the system or not. This is represented by being Offline or not.

### 3.2 Modelation of system-evolution events
- A Train Car can move or be split from its succesor. If it is the Head of the train, it can lose or restore the connection to the system and send an update about its position.
- When a Car is the Head of the train and the next Track is free, it can move. If the Car is not the Head, it can only move if it is still connected to the Head and its successor is in the next Track. Moving consists in going to the next Track. If it's the Head and it isn't Offline, update the position.
- Updating the position consists in...
- A Train Car can be split from its successors, resulting in stopping moving and the Head of the train no longer knowing its position.
- Losing the connection to the system consists in setting the Head of the train as Offline. Restoring the connection consists in unsetting that.

### 3.3 Validation of behavioral model
#### Run commands 
To ensure the accuracy and reliability of our behavioral model, we have defined specific run commands to explore scenarios involving train movement, connection status changes, and VSS state calculations. These commands simulate system interactions, allowing us to verify that the behavioral model behaves as intended under different circumstances and helping us to assess the correctness of our model's implementation and identify any potential issues or discrepancies that may arise during system operation.
Additionally, we use themes to aid in visualizing dynamic elements and events within the system, enhancing our understanding of the model's behavior.
The following run command was utilized to validate our behavioral model:
TODO: CHANGEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEE

```
run {
    some Track
    some TrainCar
    some succ
    some succs
} for 10
```

#### Themes definition
Specifically, the definitions of each section of the themes file were specified in the structural section of our report. These definitions include:

TODO: NOT SURE WHAT TO PUT HERE AS BEHAVIORAL


### 3.4 Specification and Verification of behavioral properties


## 4. Conclusion
By doing bla bla bla we were able to exercise structural and behavioral modeling, validation, and verification techniques using alloy