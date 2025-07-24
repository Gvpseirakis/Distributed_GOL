import stomp
import std/net
import rdstdin
import marshal
import strutils

type Partition = object
  rowStart: int
  rowEnd: int
  columnStart: int
  columnEnd: int

var username, password, address: string
var activeNodesPerRow: seq[int]
var rowLength: int
var sub_row, sub_col: int = 0
var isFirstNode = true

var partitionTable: seq[seq[Partition]]

# Announce when we're connected.
proc connected( c: StompClient, r: StompResponse ) =
   echo "Connected to a ", c["server"], " server."

proc initialize() =

  let creds = open("./credentials.txt")
  defer: creds.close()
  address = creds.readLine()
  username = creds.readLine()
  password = creds.readLine()


proc infoMessage( c: StompClient, r: StompResponse ) =
  let id = r[ "ack" ]

  try:
    partitionTable = to[seq[seq[Partition]]](r.payload)
    rowLength = parseInt(r["row-len"])  
    activeNodesPerRow = to[seq[int]](r["activeNodes"])
    var headers: seq[ tuple[name:string, value:string] ]
    headers.add(("row-len", r["row-len"]))
    c.send( "/topic/clientinfo", r["activeNodes"], "text/plain", headers )
  except CatchableError as e:
     let
       e = getCurrentException()
       msg = getCurrentExceptionMsg()
     echo "Got exception ", repr(e), " with message ", msg
     c.nack( id )
     return

  
  c.ack( id )

proc nodeDataMessage( c: StompClient, r: StompResponse ) =
  let id = r[ "ack" ]

  try:
     var headers: seq[ tuple[name:string, value:string] ]
     headers.add(("matrix-len", r["matrix-len"]))
     headers.add(("node-num", r["node-num"]))
     headers.add(("layers", r["layers"]))
     headers.add(("mem-use", r["mem-use"]))
     c.send( "/topic/nodeinit", r.payload, "text/plain", headers )
  except CatchableError as e:
     let
       e = getCurrentException()
       msg = getCurrentExceptionMsg()
     echo "Got exception ", repr(e), " with message ", msg
     c.nack( id )
     return

  
  c.ack( id )


proc messageLoop( c: StompClient, r: StompResponse ) =
  let id = r[ "ack" ]

  var prefetch: seq[ tuple[name:string, value:string] ]
  prefetch.add( ("prefetch-count", $1) )

  try:
    var messageType = parseInt(r["type"])  
    case messageType:
      of 1:
        var headers: seq[ tuple[name:string, value:string] ]
        headers.add(("pos-row", r["pos-row"]))
        headers.add(("type", r["type"]))
        headers.add(("pos-column", r["pos-column"]))
        c.send( "/topic/clientmessage", r.payload, "text/plain", headers )
      of 2:
        if not isFirstNode:
          c.unsubscribe( "/topic/" & $sub_row & "." & $sub_col)

        echo "Subbing to new node"
        var newNode = to[seq[int]](r.payload)
        c.subscribe( "/topic/" & $newNode[0] & "." & $newNode[1], "client-individual", "", prefetch )
        sub_row = newNode[0]
        sub_col = newNode[1]

        isFirstNode = false
      of 3:
        let cellPos_row = parseInt(r["cell-row"])
        let cellPos_col = parseInt(r["cell-col"])
        for i in 0 ..< activeNodesPerRow.len:
          for j in 0 ..< activeNodesPerRow[i]:
            if cellPos_row >= partitionTable[i][j].rowStart and cellPos_row <= partitionTable[i][j].rowEnd and cellPos_col >= partitionTable[i][j].columnStart and cellPos_col <= partitionTable[i][j].columnEnd:
              let cellPos_row_node = cellPos_row - partitionTable[i][j].rowStart
              let cellPos_col_node = cellPos_row - partitionTable[i][j].columnStart
              var headers: seq[ tuple[name:string, value:string] ]
              headers.add(("cell-row", $cellPos_row_node))
              headers.add(("cell-col", $cellPos_col_node))
              headers.add(("layer", r["layer"]))
              headers.add(("type", $3))
              c.send( "/topic/" & $i & "." & $j, $0, "text/plain", headers )
      of 4:
        let cellPos_row = parseInt(r["cell-row"])
        let cellPos_col = parseInt(r["cell-col"])
        for i in 0 ..< activeNodesPerRow.len:
          for j in 0 ..< activeNodesPerRow[i]:
            if cellPos_row >= partitionTable[i][j].rowStart and cellPos_row <= partitionTable[i][j].rowEnd and cellPos_col >= partitionTable[i][j].columnStart and cellPos_col <= partitionTable[i][j].columnEnd:
              let cellPos_row_node = cellPos_row - partitionTable[i][j].rowStart
              let cellPos_col_node = cellPos_row - partitionTable[i][j].columnStart
              var headers: seq[ tuple[name:string, value:string] ]
              headers.add(("cell-row", $cellPos_row_node))
              headers.add(("cell-col", $cellPos_col_node))
              headers.add(("layer", r["layer"]))
              headers.add(("type", $4))
              c.send( "/topic/" & $i & "." & $j, $r.payload, "text/plain", headers )
      else:
        c.unsubscribe( "/topic/" & $sub_row & "." & $sub_col)

  except CatchableError as e:
     let
       e = getCurrentException()
       msg = getCurrentExceptionMsg()
     echo "Got exception ", repr(e), " with message ", msg
     var h = readLineFromStdin("> ")
     c.nack( id )
     return

  
  c.ack( id )  


proc main() =

  initialize()
  let socket = newSocket()
  
  let uri = "stomp://" & username & ":" & password & "@" & address & "/"
  
  var client = newStompClient( socket, uri )

  # Attach callbacks
  client.connected_callback = connected
  client.connect

  var prefetch: seq[ tuple[name:string, value:string] ]
  prefetch.add( ("prefetch-count", $1) )
  
  client.message_callback = nodeDataMessage

  client.subscribe( "/topic/gatewaynodeinit", "client-individual", "", prefetch )

  client.wait_for_messages(false)

  client.unsubscribe( "/topic/gatewaynodeinit")

  client.message_callback = infoMessage

  client.subscribe( "/topic/gatewayinfo", "client-individual", "", prefetch )

  client.wait_for_messages(false)

  client.unsubscribe("/topic/gatewayinfo")

  client.subscribe( "/topic/clientrequest", "client-individual", "", prefetch )

  client.message_callback = messageLoop

  client.wait_for_messages()






main()