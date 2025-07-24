#!nimrod


import
   std/[net,json],
   stomp,
   strutils,
   sequtils,
   std/[os,random],
   marshal,
   rdstdin,
   sysinfo,
   std/monotimes,
   macros

when NimMajor < 2:
  import system/io

from times import inMilliseconds


var username, password, address: string
var node_position_row, node_position_column: int
var nodes_length_row, nodes_length_column: int

var nodeDataLengthSelf: seq[int]

var neighbourNodes: int = 0
var totalNodes: int = 1
var nodesParsed: int = 0
var activeNodesPerRow: seq[int]

var wasInterrupted: bool = false

var neighbourData: seq[seq[int]]
var gameField: seq[seq[seq[int]]]

var initData: seq[seq[int]]
var isRandom: bool = true
var gameStep: int
var gameLayers: int

var cellValueChange: tuple[layer, row, column, value:int] = (-1, -1, -1, -1)

var layerPointers: seq[ptr seq[seq[int]]]

#----------------------------------------------------------------------------BENCHMARK-----------------------------------------------------------------------------------------------------
const cLOOPS {.intdefine.} = 1225

# avoids some "bit-twiddling" for better speed...
const cBITMSK = [ 1'u8, 2, 4, 8, 16, 32, 64, 128 ]

macro unrollLoops(ca, sz, strtndx, bp: untyped) =
  let cmpstsalmtid = newIdentNode("cmpstsalmt")
  let szbitsid = newIdentNode("szbits")
  let strtndx0id = newIdentNode("strtndx0")
  let strt0id = newIdentNode("strt0")
  let strt7id = newIdentNode("strt7")
  let endalmtid = newIdentNode("endalmt")
  let bpintid = newIdentNode("bpint")
  let cullaid = newIdentNode("culla")
  result = quote do:
    let `szbitsid` = `sz` shl 3
    let `cmpstsalmtid` = `ca` + `sz`
    let `bpintid` = `bp`.int
    let `strtndx0id` = `strtndx`
    let `strt0id` = `strtndx0id` shr 3
  for i in 1 .. 7:
    let strtndxido = newIdentNode("strtndx" & $(i - 1))
    let strtndxidn = newIdentNode("strtndx" & $i)
    let strtid = newIdentNode("strt" & $i)
    result.add quote do:
      let `strtndxidn` = `strtndxido` + `bp`
      let `strtid` = (`strtndxidn` shr 3) - `strt0id`
  let csstmnt = quote do:
    case (((`bpintid` and 0x6) shl 2) + (`strtndx0id` and 7)).uint8
    of 0'u8: break
  csstmnt.del 1 # delete last dummy "of"
  for n in 0'u8 .. 0x3F'u8: # actually used cases...
    let pn = (n shr 2) or 1'u8
    let cn = n and 7'u8
    let mod0id = newLit(cn)
    let cptr0id = "cptr0".newIdentNode
    let loopstmnts = nnkStmtList.newTree()
    for i in 0'u8 .. 7'u8:
      let mskid = newLit(1'u8 shl ((cn + pn * i.uint8) and 7).int)
      let cptrid = ("cptr" & $i).newIdentNode
      let strtid = ("strt" & $i).newIdentNode
      if i == 0'u8:
        loopstmnts.add quote do:
          let `cptrid` = cast[ptr uint8](`cullaid`)
      else:      
        loopstmnts.add quote do:
          let `cptrid` = cast[ptr uint8](`cullaid` + `strtid`)
      loopstmnts.add quote do:
        `cptrid`[] = `cptrid`[] or `mskid`
    loopstmnts.add quote do:
      `cullaid` += `bpintid`
    let ofbrstmnts = quote do:
      while `cullaid` < `endalmtid`:
        `loopstmnts`
      `cullaid` = ((`cullaid` - `ca`) shl 3) or `mod0id`.int
      while `cullaid` < `szbitsid`:        
        let `cptr0id` = cast[ptr uint8](`ca` + (`cullaid` shr 3))
        `cptr0id`[] = `cptr0id`[] or cBITMSK[`cullaid` and 7]
        `cullaid` += `bpintid`
    csstmnt.add nnkOfBranch.newTree(
      newLit(n),
      ofbrstmnts
    )
  for n in 0x40'u8 .. 255'u8: # fill in defaults for remaining possibilities
    csstmnt.add nnkOfBranch.newTree(
      newLit(n),
      nnkStmtList.newTree(
        nnkBreakStmt.newTree(
          newEmptyNode()
        )
      )
    )
  result.add quote do:
    let `endalmtid` = `cmpstsalmtid` - `strt7id`
    var `cullaid` = `ca` + `strt0id`
    `csstmnt`
#  echo csstmnt[9].astGenRepr # see AST for a given case
#  echo csstmnt[9].toStrLit # see code for a given case
#  echo result.toStrLit # see entire produced code at compile time

proc benchSoE(): iterator(): int {.closure.} =
  var cmpsts = newSeq[byte](16384)
  let cmpstsa = cast[int](cmpsts[0].addr)
  for _ in 0 ..< cLOOPS:
    for i in 0 .. 254: # cull to square root of limit
      if (cmpsts[i shr 3] and cBITMSK[i and 7]) == 0'u8: # if prime -> cull its composites
        let bp = i +% i +% 3
        let swi = (i +% i) *% (i +% 3) +% 3
        unrollLoops(cmpstsa, 16384, swi, bp)
  return iterator(): int {.closure.} =
    yield 2 # the only even prime
    for i in 0 .. 131071: # separate iteration over results
      if (cmpsts[i shr 3] and cBITMSK[i and 7]) == 0'u8:
        yield i +% i +% 3
#-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------

proc cleanScreen*() =
     write(stdout,"\e[H\e[J")

proc padNeighbours() =
  for i in [0,2,6,8]:
    if neighbourData[i].len == 0: neighbourData[i].add(0)
  
  while neighbourData[3].len < nodeDataLengthSelf[0]:
    neighbourData[3].add(0)
  while neighbourData[5].len < nodeDataLengthSelf[0]:
    neighbourData[5].add(0)
  
  while neighbourData[1].len < nodeDataLengthSelf[1]:
    neighbourData[1].add(0)
  while neighbourData[7].len < nodeDataLengthSelf[1]:
    neighbourData[7].add(0)  
  

proc fillGrid(gameField: var seq[seq[int]], rows, columns: int) =
    var seed=0
    var value=0
    for i in 0 ..< rows:
        for j in 0 ..< columns:
          seed = rand(100)
          value = (int)seed>86
          gameField[i][j] = value

proc drawGrid(gameField: seq[seq[int]]) =
  cleanScreen()
  for i in 0 ..< gameField.len: #nodeDataLengthSelf[0]:
     for j in 0 ..< gameField[i].len: #nodeDataLengthSelf[1]:
         var cellState = if (bool)gameField[i][j]: "0" else: " "
         stdout.write cellState
     
     echo " "
  echo " "
  echo "Step " & $gameStep

proc rearrangeLayers() =
  var tempPtr = layerPointers[gameLayers-1]
  for i in countdown(layerPointers.len-1,1):
    layerPointers[i] = layerPointers[i-1]
  layerPointers[0] = tempPtr

proc calculateNeighbours(i,j: int, gameField: seq[seq[int]]): int =
  var neighbours = 0;
  for x in max(0, i - 1) .. min(i + 1, nodeDataLengthSelf[0]-1):
    for y in max(0, j - 1) .. min(j + 1, nodeDataLengthSelf[1]-1):
      if x != i or y != j: neighbours += gameField[x][y]

  result= neighbours

proc calculateBorders(currentStep, nextStep: var seq[seq[int]]) =
  for i in 0 ..< nodeDataLengthSelf[0]:
    var lastRowElem = nodeDataLengthSelf[1]-1
    var aliveNeighboursL = calculateNeighbours(i, 0, currentStep)
    var aliveNeighboursR = calculateNeighbours(i, lastRowElem, currentStep)

    if i == 0:
      aliveNeighboursL += neighbourData[0][0]
      aliveNeighboursL += neighbourData[1][0]
      aliveNeighboursL += neighbourData[1][1]
      aliveNeighboursR += neighbourData[2][0]
      aliveNeighboursR += neighbourData[1][lastRowElem-1]
      aliveNeighboursR += neighbourData[1][lastRowElem]

    if i == nodeDataLengthSelf[0]-1:
      aliveNeighboursL += neighbourData[6][0]
      aliveNeighboursL += neighbourData[7][0]
      aliveNeighboursL += neighbourData[7][1]
      aliveNeighboursR += neighbourData[8][0]
      aliveNeighboursR += neighbourData[7][lastRowElem-1]
      aliveNeighboursR += neighbourData[7][lastRowElem]
    else:
      aliveNeighboursL += neighbourData[3][i+1]
      aliveNeighboursR += neighbourData[5][i+1]
    
    aliveNeighboursL += neighbourData[3][i]
    aliveNeighboursR += neighbourData[5][i]
    
    nextStep[i][0] = (int)((aliveNeighboursL or currentStep[i][0]) == 3) #(int)((aliveNeighboursL == 2) or (aliveNeighboursL == 3))
    nextStep[i][lastRowElem] = (int)((aliveNeighboursR or currentStep[i][lastRowElem]) == 3) #(int)((aliveNeighboursR == 2) or (aliveNeighboursR == 3))

  for j in 0 ..< nodeDataLengthSelf[1]-1:
    var lastColumnElem = nodeDataLengthSelf[0]-1
    var aliveNeighboursU = calculateNeighbours(0, j, currentStep)
    var aliveNeighboursD = calculateNeighbours(lastColumnElem, j, currentStep)
    aliveNeighboursU += neighbourData[1][j] + neighbourData[1][j+1]
    aliveNeighboursD += neighbourData[7][j] + neighbourData[7][j+1]
    nextStep[0][j] = (int)((aliveNeighboursU or currentStep[0][j]) == 3)
    nextStep[lastColumnElem][j] = (int)((aliveNeighboursD or currentStep[lastColumnElem][j]) == 3)


proc calculateNextStep(currentStep, nextStep: var seq[seq[int]]) =

  for i in 1 ..< nodeDataLengthSelf[0]-1:
    for j in 1 ..< nodeDataLengthSelf[1]-1:
      var aliveNeighbours = calculateNeighbours(i, j, currentStep)

      nextStep[i][j] = (int)((aliveNeighbours or currentStep[i][j]) == 3)

  calculateBorders(currentStep,nextStep)

proc toSingleDimension(seqtoedit: seq[seq[int]]): seq[int] =
  #var result = newSeq[int]()
  for i in 0 ..< seqtoedit.len:
    for j in 0 ..< seqtoedit[i].len:
      result.add(seqtoedit[i][j])
  result

proc initialize() =
  randomize()

  neighbourData = newSeqWith(9, newSeq[int](1)) 

  let creds = open("./credentials.txt")
  defer: creds.close()
  node_position_row = parseInt(creds.readLine())
  node_position_column = parseInt(creds.readLine())
  nodes_length_row = parseInt(creds.readLine())
  nodes_length_column = parseInt(creds.readLine())
  address = creds.readLine()
  username = creds.readLine()
  password = creds.readLine()
  totalNodes = nodes_length_row*nodes_length_column
  nodesParsed = 0

  

  if fileExists("./positions.txt"):

    var continueStep = readLineFromStdin("The daemon was terminated unexpectedly. Continue? (Y/n): ")
    if continueStep.toUpperAscii != "Y": return
    
    wasInterrupted = true
    let positions = open("./positions.txt")
    defer: positions.close()
    node_position_row = parseInt(positions.readLine())
    node_position_column = parseInt(positions.readLine())
    nodeDataLengthSelf = to[seq[int]](positions.readLine())
    activeNodesPerRow = to[seq[int]](positions.readLine())
    if fileExists("./selfData.txt"):
      let selfDataFile  = open("selfData.txt")
      defer: selfDataFile.close()
      var selfData = to[seq[int]](selfDataFile.readLine())
      gameField = newSeq[seq[seq[int]]](gameLayers)

      var nodeData = selfData.distribute(nodeDataLengthSelf[0], false)
      layerPointers = newSeq[ptr seq[seq[int]]](gameLayers)
      for i in 0 ..< gameLayers:
        gameField[i] = nodeData
        layerPointers[i] = addr gameField[0]

  if fileExists("./parsed.txt"):    
    let parsedFile = open("parsed.txt")
    defer: parsedFile.close()
    nodesParsed = parseInt(parsedFile.readLine())
    gameStep = parseInt(parsedFile.readLine())
    #todo: read more stuff here(neighbours,self data)

  for i in 0 .. 8:
    if fileExists($i & "data.txt"):
      let dataFile = open($i & "data.txt")
      defer: dataFile.close()
      var data = to[seq[int]](dataFile.readLine())
      neighbourData[i] = data
  


  

# Announce when we're connected.
proc connected( c: StompClient, r: StompResponse ) =
   echo "Connected to a ", c["server"], " server."
   



#NETWORK STEP 3: send the specs that were requested
proc specMessage( c: StompClient, r: StompResponse ) =
  let id = r[ "ack" ]
  var allowedMemoryUsage: float
  
  try:
     allowedMemoryUsage = parseFloat(r.payload) 
  except CatchableError as e:
     echo "Couldn't parse! ", r.payload
     c.nack( id )
  
  GC_fullcollect()
  var allowedLocalMem = float(getFreeMemory())
  let allowedNodeMem = (int)(allowedLocalMem*allowedMemoryUsage)
  #echo $(allowedLocalMem, allowedNodeMem)
  #var ss = readLineFromStdin("ses")
  var cpu = getCpuName().replace("(TM)", "").replace("(R)", "").replace("CPU ", "")
  
  let strt = getMonotime()
  let answr = benchSoE()
  var cnt = 0; for _ in answr(): cnt += 1
  var elpsd = float((getMonotime() - strt).inMilliseconds)
  elpsd = 100/elpsd

  
  var headers: seq[ tuple[name:string, value:string] ]
  headers.add( ("mem", $allowedNodeMem) )
  headers.add( ("bench", $elpsd) )
  headers.add( ("pos-row", $node_position_row) )
  headers.add( ("pos-column", $node_position_column) )
  c.send( "/topic/specshare", cpu, "text/plain", headers )
  c.ack( id )

#NETWORK STEP 7: process the new position and data
proc infoMessage( c: StompClient, r: StompResponse ) =
  let id = r[ "ack" ]
  var isActive = parseInt(r["isActive"])
  if not bool(isActive):
    echo "Not part of the grid. Terminating."
    c.ack( id )
    system.quit()  

  var oldRow = node_position_row
  var oldColumn = node_position_column
  echo $r["activeNodes"]

  node_position_row = parseInt(r["pos-row"])
  node_position_column = parseInt(r["pos-column"])
  nodeDataLengthSelf = to[seq[int]](r["dimensions"])

  activeNodesPerRow = to[seq[int]](r["activeNodes"])
  gameLayers = parseInt(r["layers"])

  var data = to[seq[int]](r.payload)
  if data.len > 0:
    isRandom = false
  initData = data.distribute(nodeDataLengthSelf[0],false)


  
  layerPointers = newSeq[ptr seq[seq[int]]](gameLayers)
  gameField = newSeq[seq[seq[int]]](gameLayers)
  for i in 0 ..< gameLayers:
    gameField[i] = newSeqWith(nodeDataLengthSelf[0], newSeq[int](nodeDataLengthSelf[1]))
    layerPointers[i] = addr gameField[i]
  
  c.ack( id )

  let positions = open("positions.txt", fmWrite)
  defer: positions.close()
  positions.writeLine($node_position_row)
  positions.writeLine($node_position_column)
  positions.writeLine(r["dimensions"])
  positions.writeLine(r.payload)
  
  
  sleep(100)
  c.unsubscribe( "/topic/info" & $oldRow & "." & $oldColumn)

proc dataMessageLoop( c: StompClient, r: StompResponse ) =

  sleep(1000)
  let id = r[ "ack" ]
  
  let msgType = parseInt(r["type"])
  if msgType == 3:
    let cellPos_row = parseInt(r["cell-row"])
    let cellPos_col = parseInt(r["cell-col"])
    let layer = parseInt(r["layer"])
    var headers: seq[ tuple[name:string, value:string] ]
    headers.add( ("type", $3) )
    c.send( "/topic/clientmessage", $layerPointers[layer][][cellPos_row][cellPos_col], "text/plain", headers )
    c.ack( id )
    return
  if msgType == 4:
    let cellPos_row = parseInt(r["cell-row"])
    let cellPos_col = parseInt(r["cell-col"])
    let layer = parseInt(r["layer"])
    var valueToSet = parseInt(r.payload)
    cellValueChange = (layer, cellPos_row, cellPos_col, valueToSet)
    c.ack( id )
    return
  
  
  
  try:
    let rowActual = parseInt(r["pos-row"])
    let columnActual: int = parseInt(r["pos-column"])

    #if rowActual == node_position_row and columnActual == node_position_column: return
  
    let relativePosition_row = rowActual-node_position_row+1
    let relativePosition_column = columnActual-node_position_column+1
    let singleRelativeIndex = relativePosition_column + 3*relativePosition_row
    var nodeData = to[seq[int]](r.payload).distribute(nodeDataLengthSelf[0], false)
    neighbourData[singleRelativeIndex] = @[]
    var datavalue: int
    if 3 <= singleRelativeIndex and singleRelativeIndex <= 5:
      
      for i in 0 ..< min(nodeData.len,nodeDataLengthSelf[0]):       
        datavalue = nodeData[i][(nodeData[i].len-1)*(int)(singleRelativeIndex==3)]
        neighbourData[singleRelativeIndex].add(datavalue)
    elif singleRelativeIndex mod 3 == 1:
      for i in 0 ..< min(nodeData[0].len,nodeDataLengthSelf[1]):
        datavalue = nodeData[(nodeData.len-1)*(int)(singleRelativeIndex==1)][i]
        neighbourData[singleRelativeIndex].add(datavalue)
    else:
      datavalue = nodeData[(nodeData.len-1)*(int)(relativePosition_row != 2)][(nodeData[0].len-1)*(int)(relativePosition_column != 2)]
      neighbourData[singleRelativeIndex].add(datavalue)

    let dataFile = open($singleRelativeIndex & "data.txt", fmWrite)
    defer: dataFile.close()
    dataFile.writeLine($$neighbourData[singleRelativeIndex])

    nodesParsed += 1
    let parsedFile = open("parsed.txt", fmWrite)
    defer: parsedFile.close()
    parsedFile.writeLine($nodesParsed)
    parsedFile.writeLine($gameStep)
    c.ack( id ) 

  except CatchableError as e:
    let
     e = getCurrentException()
     msg = getCurrentExceptionMsg()
    echo "Got exception ", repr(e), " with message ", msg
    c.nack( id )
    return
  #do stuff
           
  if nodesParsed == neighbourNodes:
    padNeighbours()

    var headers: seq[ tuple[name:string, value:string] ]
    headers.add( ("pos-row", $node_position_row) )
    headers.add( ("pos-column", $node_position_column) )
    headers.add( ("type", $1) )
    var nodeDataToSend: seq[int]

    calculateNextStep(layerPointers[0][], layerPointers[gameLayers-1][])
    if cellValueChange.row >= 0:
      layerPointers[cellValueChange.layer][][cellValueChange.row][cellValueChange.column]= cellValueChange.value
    rearrangeLayers()
    

    cellValueChange.row = -1

    if gameStep == high(int):
      gameStep = 1
    else:
      gameStep += 1
    
    drawGrid(layerPointers[0][])
    nodeDataToSend = toSingleDimension(layerPointers[0][])
    
    #$validation 
    if gameStep == 50:
      let validateFile = open($node_position_row & $node_position_column & "values.txt", fmWrite)
      defer: validateFile.close()
      validateFile.writeLine($$layerPointers[0][])
      var h = readLineFromStdin("> ")

    nodesParsed = 0
    
    c.send( "/topic/" & $node_position_row & "." & $node_position_column, $$nodeDataToSend, "text/plain", headers )
    let parsedFile = open("parsed.txt", fmWrite)
    defer: parsedFile.close()
    parsedFile.writeLine($nodesParsed)
    parsedFile.writeLine($gameStep)

    let selfDataFile  = open("selfData.txt", fmWrite)
    defer: selfDataFile.close()
    selfDataFile.writeLine($$nodeDataToSend)
  



proc subscribeToBlock( c: StompClient, prefetchHeaders: seq[ tuple[name:string, value:string] ]) =
  neighbourNodes = 0
  for x in max(0, node_position_row - 1) .. min(node_position_row + 1, activeNodesPerRow.len - 1):
        for y in max(0, node_position_column - 1) .. min(node_position_column + 1, activeNodesPerRow[x] - 1):
          if (x != node_position_row) or (y != node_position_column):
            neighbourNodes += 1
            c.subscribe( "/topic/" & $x & "." & $y, "client-individual", "", prefetchHeaders )



proc main() =
  wasInterrupted = false

  initialize()
  
  let socket = newSocket()
  
  let uri = "stomp://" & username & ":" & password & "@" & address & "/"
  
  var client = newStompClient( socket, uri )
  # Attach callbacks
  client.connected_callback = connected

  var prefetch: seq[ tuple[name:string, value:string] ]
  prefetch.add( ("prefetch-count", $1) )

  var headers: seq[ tuple[name:string, value:string] ]
  headers.add( ("pos-row", $node_position_row) )
  headers.add( ("pos-column", $node_position_column) )
  headers.add( ("type", $1) )
 

  if wasInterrupted:
    client.connect
    subscribeToBlock(client, prefetch)
    client.message_callback = dataMessageLoop
    
    if nodesParsed == neighbourNodes:
      var nodeDataToSend = toSingleDimension(layerPointers[0][])
      client.send( "/topic/" & $node_position_row & "." & $node_position_column, $$nodeDataToSend, "text/plain", headers )
      nodesParsed = 0

    client.wait_for_messages()
    return

      
  try:
    
    nodesParsed = 0 
    
    #NETWORK STEP 1: subscribe to the spec request that the parent node is going to send and wait
    client.message_callback = specMessage
    # Open a session with the broker
    client.connect
    client.subscribe( "/topic/specrequest", "client-individual", "", prefetch )
    client.wait_for_messages(false)

  
    client.unsubscribe( "/topic/specrequest")

    #NETWORK STEP 5: subscribe and wait for the information
    nodesParsed = 0
    client.message_callback = infoMessage
    client.subscribe( "/topic/info" & $node_position_row & "." & $node_position_column, "client-individual", "", prefetch )
    client.wait_for_messages(false)
  except CatchableError:
    let
      e = getCurrentException()
      msg = getCurrentExceptionMsg()
    echo "Got exception ", repr(e), " with message ", msg


  subscribeToBlock(client, prefetch)

  if isRandom:
    fillGrid(layerPointers[0][], nodeDataLengthSelf[0], nodeDataLengthSelf[1])
  else:
    layerPointers[0][] = initData

  gameStep += 1    
  drawGrid(layerPointers[0][]) 

  


  sleep(1000)
  var nodeDataToSend = toSingleDimension(layerPointers[0][])
  
  client.send( "/topic/" & $node_position_row & "." & $node_position_column, $$nodeDataToSend, "text/plain", headers )
  
  
  client.message_callback = dataMessageLoop
  nodeDataToSend.setLen(0)
  GC_fullcollect()
    
  nodesParsed = 0
  client.wait_for_messages()


main()
