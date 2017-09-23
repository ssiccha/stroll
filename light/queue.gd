#############################################################################
##
##                             parorb package
##  stack.gd
##                                            Sergio Siccha, Matthias Koch
##
##  Copyright...
##
##  Declaring for queue.gi
##
#############################################################################

DeclareFilter("IsQueue");
DeclareFilter("IsQueueNode");

DeclareOperation("QueueCreate", [ IsObject ] );
DeclareOperation("QueuePushBack", [ IsQueue and IsMutable, IsObject ]);
DeclareOperation("QueuePopFront", [ IsQueue and IsMutable] );
DeclareOperation("QueueClear", [ IsQueue and IsMutable]);
DeclareOperation("QueueFront", [ IsQueue ]);
DeclareOperation("QueueBack", [ IsQueue ]);
DeclareOperation("QueueEmpty", [ IsQueue ]);


