# This example shows how to draw the surface of a control.
import std/net
import nigui
import threadpool
import stomp
import strutils
import sequtils
import marshal
import rdstdin
import std/math


const WINDOW_WIDTH = 1200
const WINDOW_HEIGHT = 1000

var gameCanvas: Canvas
var gameStateImage: Image
var control1: Control
var client: StompClient
var comboBoxRow: ComboBox
var comboBoxColumn: ComboBox
var window: Window

var observingNode = false

let socket = newSocket()


var username, password, address: string
var activeNodesPerRow: seq[int]
var rowLength: int
var sub_row, sub_col: int
var gameState: seq[seq[int]]
var widthOffset, heightOffset: int = 800
      
proc readCell(layer,cellRow, cellCol: int) = 
  var headers: seq[ tuple[name:string, value:string] ]
  headers.add(("cell-row", $cellRow))
  headers.add(("cell-col", $cellCol))
  headers.add(("layer", $layer))
  headers.add(("type", $3))
  client.send( "/topic/clientrequest", $0, "text/plain", headers )

proc writeCell(layer, cellRow, cellCol, value: int) = 
  var headers: seq[ tuple[name:string, value:string] ]
  headers.add(("cell-row", $cellRow))
  headers.add(("cell-col", $cellCol))
  headers.add(("layer", $layer))
  headers.add(("type", $4))
  client.send( "/topic/clientrequest", $value, "text/plain", headers )

# Announce when we're connected.
proc connected( c: StompClient, r: StompResponse ) =
   echo "Connected to a ", c["server"], " server."


proc infoMessage( c: StompClient, r: StompResponse ) =
  let id = r[ "ack" ]

  try:
    rowLength = parseInt(r["row-len"])  
    activeNodesPerRow = to[seq[int]](r.payload)  
  except CatchableError as e:
    echo "Couldn't parse! ", r.payload
    c.nack( id )

  var rows: seq[string]
  for i in 0 ..< activeNodesPerRow.len:
    rows.add($i)

  comboBoxRow.options = rows


  var columns: seq[string]
  if activeNodesPerRow.len > 0:
    for i in 0 ..< activeNodesPerRow[0]:
      columns.add($i)

  comboBoxColumn.options = columns
  c.ack(id)


proc messageLoop( c: StompClient, r: StompResponse ) =
  let id = r[ "ack" ]
  let messageType = parseInt(r["type"])  

  if messageType == 3:
    echo "the cell value is: " & r.payload
    c.ack(id)
    return
    
  if (not observingNode):
    c.ack(id)
    return

  try:
    gameState = to[seq[int]](r.payload).distribute(rowLength, false)
    
    
    widthOffset = floorDiv(min(800,gameState[0].len), 2)
    heightOffset = floorDiv(min(800,gameState.len), 2)

    for i in 0 ..< min(800,gameState.len):
      for j in 0 ..< min(800,gameState[i].len):
        if (bool)gameState[i][j]: 
          gameStateImage.canvas.setPixel(j, i, rgb(45, 220, 0))
        else: 
          gameStateImage.canvas.setPixel(j, i, rgb(30, 30, 30))

    control1.forceRedraw()
  except CatchableError as e:
     let
       e = getCurrentException()
       msg = getCurrentExceptionMsg()
     echo "Got exception ", repr(e), " with message ", msg
     var h = readLineFromStdin("> ")
     c.nack( id )
     return

  c.ack(id)


proc initWorld() =
  
  echo "Choose the initialization plan: "
  echo "1. Random values"
  echo "2. Load values from file (values.txt)"

  var choice = "0"
  while choice != "1" and choice != "2":
    choice =  readLineFromStdin("> ")
  
  var values: seq[int]
  var matrixLength: int
  if choice == "2":
    let valueFile = open("./values.txt")
    defer: valueFile.close()
    values = to[seq[int]](valueFile.readLine())
    matrixLength = (int)sqrt((float)values.len)
    echo "matrix length= " & $matrixLength
  else:
    matrixLength = readLineFromStdin("Enter the size of the square matrix NxN. N= ").parseInt()
  
  var nodeNumber = readLineFromStdin("Enter gridworld size NxN (0 to calculate based on memory) N= ").parseInt()
  var allowedMemoryUsage: float
  if nodeNumber == 0:
    allowedMemoryUsage = readLineFromStdin("Enter the percentage of free memory to be used:  ").parseFloat()
    allowedMemoryUsage /= 100
  
  var layers:int = 0
  while layers < 2:
    layers =  readLineFromStdin("Enter the number of layers: ").parseInt()

  var headers: seq[ tuple[name:string, value:string] ]
  headers.add(("matrix-len", $matrixLength))
  headers.add(("node-num", $nodeNumber))
  headers.add(("layers", $layers))
  headers.add(("mem-use", $allowedMemoryUsage))

  client.send( "/topic/gatewaynodeinit", $$values, "text/plain", headers )   
         

proc generateNodeData() {.thread.} =
  {.cast(gcsafe).}:
    
    let uri = "stomp://" & username & ":" & password & "@" & address & "/"
  
    client = newStompClient( socket, uri )
    
    # Attach callbacks
    client.connected_callback = connected
    client.connect

    initWorld()

    client.message_callback = infoMessage
  
    client.subscribe( "/topic/clientinfo", "client-individual" )
    client.wait_for_messages(false)
    
    client.message_callback = messageLoop

    client.unsubscribe( "/topic/clientinfo")
    

    client.wait_for_messages()

  

proc controlDrawn(event: DrawEvent) = 
    gameCanvas = event.control.canvas
    # A shortcut
  
    gameCanvas.areaColor = rgb(30, 30, 30) # dark grey
    gameCanvas.fill()
    
    gameCanvas.textColor = rgb(0, 255, 0) 
    gameCanvas.fontSize = 20
    gameCanvas.fontFamily = "Arial"

    
    var image_x = floorDiv(WINDOW_WIDTH, 2) - widthOffset
    var image_y = floorDiv(WINDOW_HEIGHT, 2) - heightOffset

    gameCanvas.drawImage(gameStateImage, image_x, image_y)


proc nodeDiscarded(event: CloseClickEvent) =
  observingNode = false
  client.unsubscribe( "/topic/clientmessage")
  window.dispose()


proc drawGraphics()  = 
  #{.cast(gcsafe).}:
    
  window = newWindow()
  window.width = WINDOW_WIDTH
  window.height = WINDOW_HEIGHT
  
  control1 = newControl()

  
  control1.widthMode = WidthMode_Fill
  control1.heightMode = HeightMode_Fill
  
  window.add(control1)
  
  window.onCloseClick = nodeDiscarded
  
  control1.onDraw = controlDrawn
  
  gameStateImage = newImage()
  gameStateImage.resize(800, 800)
  for i in 0 ..< 800:
    for j in 0 ..< 800:
      gameStateImage.canvas.setPixel(i, j, rgb(30, 30, 30))

  window.show()


proc nodeSelected(event: ClickEvent) =
  if comboBoxColumn.options.len == 0 or comboBoxRow.options.len == 0: return

  observingNode = true

  drawGraphics()

  var row = comboBoxRow.index
  var column = comboBoxColumn.index
  

  var headers: seq[ tuple[name:string, value:string] ]
  headers.add( ("type", $2) )
  var payload: seq[int]
  payload.add(row)
  payload.add(column)

  client.send("/topic/clientrequest", $$payload, "text/plain", headers )

  var prefetch: seq[ tuple[name:string, value:string] ]
  prefetch.add( ("prefetch-count", $1) )
  client.subscribe( "/topic/clientmessage", "client-individual", "", prefetch )




proc rowChanged(event: ComboBoxChangeEvent) = 
  var index = comboBoxRow.index
  var columns: seq[string]
  for i in 0 ..< activeNodesPerRow[index]:
    columns.add($i)

  comboBoxColumn.options = columns
  comboBoxColumn.index = 0
  
  
proc drawMenu() {.thread.}  = 
  {.cast(gcsafe).}:
    app.init()
  
    var menuwidow = newWindow()
    menuwidow.width = 160
    menuwidow.height = 160
    
    var container1 = newLayoutContainer(Layout_Horizontal)
  
    var label1 = newLabel("Node row:      ")
    container1.add(label1)
    comboBoxRow = newComboBox()
    container1.add(comboBoxRow)
    
    comboBoxRow.onChange = rowChanged

    var container2 = newLayoutContainer(Layout_Horizontal)
    
    var label2 = newLabel("Node column: ")
    container2.add(label2)
    comboBoxColumn = newComboBox()
    container2.add(comboBoxColumn)
  
    var container3 = newLayoutContainer(Layout_Horizontal)

    var button = newButton("Show")
    container3.add(button)

    button.onClick = nodeSelected

    var containerMain = newLayoutContainer(Layout_Vertical)
    containerMain.add(container1)
    containerMain.add(container2)
    containerMain.add(container3)
  
    menuwidow.add(containerMain)
  
    menuwidow.show()

    app.run()


proc initialize() =

  let creds = open("./credentials.txt")
  defer: creds.close()
  address = creds.readLine()
  username = creds.readLine()
  password = creds.readLine()
    

proc main() =
  initialize()
  spawn generateNodeData()
  spawn drawMenu()
  
  sync()


main()