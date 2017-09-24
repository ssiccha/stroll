

IsSinglyLinkedListQueueRep := NewRepresentation( "IsSinglyLinkedListQueueRep", IsComponentObjectRep, [ "first", "last", "size" ]);


IsSinglyLinkedListQueueNodeRep := NewRepresentation( "IsSinglyLinkedListQueueNodeRep", IsComponentObjectRep, [ "next", "obj" ] );


QueueNodeFamily := NewFamily( "QueueNodeFamily", IsObject, IsQueueNode);
QueueFamily := NewFamily( "QueueFamily", IsObject, IsQueue);


IsSinglyLinkedListQueueNode := NewCategory( "IsSinglyLinkedListQueueNode", IsSinglyLinkedListQueueNodeRep and IsQueueNode);


IsSinglyLinkedListQueue := NewCategory( "IsSinglyLinkedListQueue", IsSinglyLinkedListQueueRep and IsQueue);



InstallMethod( QueueCreate, "constructor for a singly linked list queue",
  [],
  function()
    local queue;
    queue := rec( first := fail, last := fail, size := 0 );
    Objectify(NewType(QueueFamily,IsSinglyLinkedListQueue and IsMutable),queue);
    return queue;
  end );


InstallMethod( QueuePushBack, "push object to the end",
  [ IsMutable and IsSinglyLinkedListQueue, IsObject ],
  function( queue, object )
    local node;
    node := rec( obj := object, next := fail );
    Objectify(NewType(QueueNodeFamily,IsSinglyLinkedListQueueNode and IsMutable), node );
    if 0 = queue!.size then
      queue!.first := node;
      queue!.last := node;
    else
      queue!.last!.next := node;
      queue!.last := node;
    fi;
    queue!.size := queue!.size + 1;
  end );


InstallMethod( QueuePopFront, "pop the first object",
  [ IsMutable and IsSinglyLinkedListQueue ],
  function( queue )
    local node;
    if 0 = queue!.size then
      Error("\nThis queue is empty, QueuePopFront is not possible\n");
      return;
    fi;
    queue!.size := queue!.size - 1;
    node := queue!.first;
    queue!.first := node!.next;
    if 0 = queue!.size then
      queue!.last := fail; 
    fi;
    return node!.obj; 
  end );



InstallMethod( QueueClear, "clear all objects from queue",
  [ IsMutable and IsSinglyLinkedListQueue ],
  function( queue )
    queue!.first := fail;
    queue!.last := fail;
    queue!.size := 0;
  end );
  



InstallMethod( QueueFront, "get the first element",
  [ IsMutable and IsSinglyLinkedListQueue ],
  function( queue )
    if 0 = queue!.size then
      Error("\nThis queue is empty, QueueFront is not possible\n");
      return;
    fi;
    return queue!.first!.obj; 
  end );



InstallMethod( QueueBack, "get the last element",
  [ IsMutable and IsSinglyLinkedListQueue ],
  function( queue )
    if 0 = queue!.size then
      Error("\nThis queue is empty, QueueBack is not possible\n");
      return;
    fi;
    return queue!.last!.obj; 
  end );



InstallMethod( QueueEmpty, "checks whether the queue is empty",
  [ IsSinglyLinkedListQueue ],
  function( queue )
    return queue!.size = 0;
  end );



InstallMethod( PrintObj, "for a singly linked list queue node object",
  [ IsSinglyLinkedListQueueNode ],
  function( cn )
    Print("<singly linked list queue node obj=");
    ViewObj(cn!.obj);
    Print(">");
  end );


InstallMethod( Display, "for a singly linked list queue node object",
  [ IsSinglyLinkedListQueueNode ],
  function( queue )
    Print("<singly linked list queue node obj=");
    Display(queue!.obj);
    Print(">\n");
  end );


InstallMethod( PrintObj, "for a singly linked list queue object",
  [ IsSinglyLinkedListQueue ],
  function(c)
    Print("<singly linked list queue with ",c!.size," objects>");
  end );


InstallMethod( Display, "for a singly linked list queue object",
  [ IsSinglyLinkedListQueue ],
  function(c)
    local cn,i;
    if 0 = c!.size then
      Print("<singly linked list queue with ",c!.size," objects>\n");
    else
      Print("<singly linked list queue with ",c!.size," objects containing:\n");
      cn := c!.first;
      i := 0;
      while cn <> fail do
          i := i + 1;
          Print("\t# ",i," \tobj=");
          PrintObj(cn!.obj);
          Print("\n");
          cn := cn!.next;
      od;
      Print(">\n");
    fi;
  end );



