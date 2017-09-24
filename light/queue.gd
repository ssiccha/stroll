#############################################################################
##
##  queue.gd
##                                            Sergio Siccha, Matthias Koch
##
##
##
#############################################################################

DeclareFilter( "IsQueue" );
DeclareFilter( "IsQueueNode" );

# DeclareOperation( "QueueCreate", [] );
if not IsReadOnlyGlobal( "QueueCreate" ) then
  QueueCreate := NewConstructor( "QueueCreate", [] );
  MakeReadOnlyGlobal( "QueueCreate" );
fi;

DeclareOperation( "QueuePushBack", [ IsQueue and IsMutable, IsObject ] );
DeclareOperation( "QueuePopFront", [ IsQueue and IsMutable] );
DeclareOperation( "QueueClear", [ IsQueue and IsMutable] );
DeclareOperation( "QueueFront", [ IsQueue ] );
DeclareOperation( "QueueBack", [ IsQueue ] );
DeclareOperation( "QueueEmpty", [ IsQueue ] );


