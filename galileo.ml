open Yojson
open Core.Std

(*
================================================================================================================================
                                                                                                                               =
Code for evolving Galileo symmetric spacetimes using an iterated Crank-Nicolson scheme.                                        =
                                                                                                                               =
To the extent possible under law, Adam Layne has waived all copyright and related or neighboring rights to this work.          =
                                                                                                                               =
Compile with                                                                                                                   =
                                                                                                                               =
ocamlfind ocamlopt -linkpkg -thread -package core -package yojson galileo.ml -o galileo.native                                 =
                                                                                                                               =
================================================================================================================================
*)

let pi = Pervasives.acos (-1.)

(*

Some aliases for doing common operations on lists and arrays.

*)

let (  *||  ) b c = Array.map2_exn b c ~f:(fun x y -> x *. y) 

let (  +||  ) b c = Array.map2_exn b c ~f:(fun x y -> x +. y) 

let (  -||  ) b c = Array.map2_exn b c ~f:(fun x y -> x -. y) 

let (  /||  ) b c = Array.map2_exn b c ~f:(fun x y -> x /. y) 

let (  *.|  ) b c = Array.map c ~f:(fun y -> b *. y) 

let (  **|.  ) b c = Array.map b ~f:(fun y -> y ** c ) 

let (  +.|  ) b c = Array.map c ~f:(fun y -> b +. y) 

let (  -.|  ) b c = Array.map c ~f:(fun y -> b -. y) 

let (  /.|  ) b c = Array.map c ~f:(fun y -> b /. y) 

let arrayexp c = Array.map c ~f:(fun y -> exp y ) 

let doublearrayadd b c = Array.map2_exn b c ~f:(fun x y -> x +|| y) 

let (  +||||  ) b c = Array.map2_exn b c ~f:(fun x y -> x +|| y) 

let doublearraymultiply b c = Array.map c ~f:(fun y -> b *.| y) 

let (  *.||  ) b c = Array.map c ~f:(fun y -> b *.| y) 

let doublearraysubtract b c = doublearrayadd b ( doublearraymultiply ( -1.0 ) c )

let (  -||||  ) b c = doublearrayadd b ( doublearraymultiply ( -1.0 ) c )

let dotProductFloatArrays xs ys = Array.fold2_exn ~f:(fun c a b -> c +. a *. b) ~init:0.0 xs ys  

let arraytail ar =
  let n = Array.length ar in
  ar.(n-1)

let sum list = 
  let rec accumulating_sum list total = 
    match list with
      | [] -> total
      | head::tail -> accumulating_sum tail (head +. total) in
  accumulating_sum list 0.0

(*

An imperative array sum.

*)

let arraysum ar = 
  let n = Array.length ar in
  let total = ref 0.0 in
  let i = ref 0 in
  while !i < n do
    total := !total +. ar.(!i) ;
    incr i
  done;
  !total

let average list = (sum list) /. float(List.length list)

let range n = Array.init n ~f:(fun x -> Float.of_int(x) +. 1.0 )

(*

The following reverses an array. The one built into core is inplace.

*)

let arrayrev a =
  let len = Array.length a in
  Array.init len ~f:(fun i -> a.( len - ( i + 1 ) ) )

(*

The following shifts an array to the left by n, shortening it.

*)

let arrayshift a n = 
  if n>= 0 then 
    Array.init ( Array.length a - n ) ~f:(fun i -> a.(i+n) ) 
  else
    arrayrev(Array.init ( Array.length a + n ) ~f:(fun i -> (arrayrev(a)).(i-n) ))

(*

The following does the same as above, but pads with floats of 0..

*)

let arrayshiftpad a n =
  if n >= 0 then
    Array.append ( arrayshift a n ) ( Array.init ( n ) ~f:(fun x -> 0. ) )
  else
    Array.append ( Array.init ( -n ) ~f:(fun x -> 0. ) ) ( arrayshift a n )

(*

The depth 2 version of List.to_array and vice versa.

*)

let listtoarray2 listlist = List.to_array ( List.map listlist ~f:( fun x  -> List.to_array x ) ) 

let arraytolist2 arrayarray = Array.to_list ( Array.map arrayarray ~f:( fun x  -> Array.to_list x ) ) 

(*

As we were programming the evolution code, we realized that we're having dumb difficulties related to the "extra points" problem. That is, to use finite difference schemes on the circle, it's necessary to look beyond the bounds of the array at some points. The way I'm solving this problem is to keep an array with only a unique representative of each point. Then when more are needed, create such an array. That is what the following code does.

*)

let arrayunroll data points =
  let length = Array.length data in
  Array.init ( length + 2 * points ) ~f:(fun i -> data.( ( i - points + length ) mod length ) )

(*

A first derivative. This runs much faster than the old version, but isn't as flexible or explicit.

We started with a flexible piece of code that computed nth derivatives to kth order accuracy, but it ran too slow.

*)

let first_derivative_4th_order ~valuearray ~delta = 
  let h = arrayunroll valuearray 2 in
  Array.init ( Array.length valuearray ) ~f:( fun i -> ( 2.0 /. 3.0 *. ( h.(i+3) -. h.(i+1) ) +. 1.0 /. 12.0 *. ( h.(i) -. h.(i+4) ) ) /. delta )


(*

A second derivative.

*)

let second_derivative_4th_order ~valuearray ~delta = 
  let h = arrayunroll valuearray 2 in
  Array.init ( Array.length valuearray ) ~f:( fun i -> ( -2.5 *. h.(i+2) +. 4.0 /. 3.0 *. ( h.(i+1) +. h.(i+3) ) -. 1.0 /. 12.0 *. ( h.(i) +. h.(i+4) ) ) /. ( delta *. delta ) )

(*

The following are bits of code we often use for testing purposes.

*)

let absfloatmax a = Array.fold a ~init:0.0 ~f:( fun x y -> Float.max x ( Float.abs y ) )

let absfloatmax2 a = absfloatmax ( Array.map a ~f:( fun x -> absfloatmax x ) )

let absfloatmin a = Array.fold a ~init:Float.infinity ~f:( fun x y -> Float.min x ( Float.abs y ) )

let absfloatmin2 a = absfloatmin ( Array.map a ~f:( fun x -> absfloatmin x ) )

(*

Next, we need something to handle file input and output.

We store the data in JSON format. At each time, the data is represented by a time_frame type, defined below as type time_frame = { time : float ; data : float array array }. time_frame.data.(0) is the list of the data for the first function at each spatial point, and time_frame.data.(1) is the second function and so on. A type called evolution is defined further down. It includes some front matter, and then a time_frame array, storing the time frames at different times. The front matter can contain anything, and the functions further down are written to pass this on unmodified. In our case, the front matter will sometimes contain the Fourier ceofficients of the initial data, and the time that that initial data is at. Here is an acceptable input file for a 2 function evolution.

{
  "initial time": 0.0,
  "fourier coefficients": [
    {
      "sine": [ -1.22237 , 1.23632 ] , "cosine": [ 0.92248 , -0.65116 , -1.22724 ]
    },
    {
      "sine": [ 0.1646087175085454 , -0.12946909856220498 ], "cosine": [ -0.60093 , 0.11178843444197277 , 0.09136379176387607 ]
    }
  ],
  "evolution": [
    {
      "time": 1.0 , "data": [ [ 0.0 , 0.0 , 0.0 , 0.0 ] , [ 6.731691327841086 , 6.65606276702008 , 6.578397100691003 , 6.498744619898678 ] ]
    },
    {
      "time": 2.9757672547967196 , "data": [ [ -2.3773404404336578 , -2.3647802342902766 , -2.351606331335206 , -2.3378108740811374 ] , [ 2.852714020049776 , 2.456794296433753 , 2.0568919397268304 , 1.6576549796900544 ] ]
    }
  ]
}

*)

type time_frame = { time : float ; data : float array array }

(*

Algebra with time_frames.

*)

let (  +>>  ) b c = 
  { 
    time = b.time +. c.time ;
    data = b.data +|||| c.data
  }

let (  *.>  ) b c = 
  { 
    time = b *. c.time ;
    data = b *.|| c.data
  }

let (  ->>  ) b c = b +>> ( (-1.0) *.> c )

(*

Increments one frame one step according to the hardcoded PDE. Recall that the functions are stored in the array as


				function	P	π_P	Q	π_Q	λ	π_λ
				index		0	1	2	3	4	5


*)

let changeframe frame deltat deltax accuracy =
  let exp c = Pervasives.exp c in
  let d0 = frame.data in
  let n = Array.length ( d0.(0) ) in
  let t = frame.time in
  let d10 = first_derivative_4th_order d0.(0) deltax  in 
  let d12 = first_derivative_4th_order d0.(2) deltax  in 
  let d15 = first_derivative_4th_order d0.(5) deltax  in 
  let d20 = second_derivative_4th_order d0.(0) deltax in 
  let d22 = second_derivative_4th_order d0.(2) deltax in 
  let dt0 i =   -1.0 *. d0.(1).(i) /. ( 2.0 *. d0.(5).(i) )  in
  let dt1 i =   -1.0 /. ( 2.0 *. d0.(5).(i) ) *.	(
                                                          exp( -2.0 *. d0.(0).(i) ) *. d0.(3).(i) *. d0.(3).(i)
                                                          +. exp( 2.0 *. t ) *. d20.(i)
                                                          -. exp( 2.0 *. t ) *. d10.(i) *. d15.(i) /. d0.(5).(i)
                                                          -. exp( 2.0 *. ( d0.(0).(i) +. t ) ) *. d12.(i) *. d12.(i)
							)
							+.  d0.(5).(i) *. exp( ( d0.(4).(i) +. 2.0 *. d0.(0).(i) -. 3.0 *. t ) /. 2.0 )
  in
  let dt2 i =    -1.0 *. exp( -2.0 *. d0.(0).(i) ) *. d0.(3).(i) /. ( 2.0 *. d0.(5).(i) )
  in
  let dt3 i =    -1.0 *. exp( 2.0 *. ( d0.(0).(i) +. t ) ) /. ( 2.0 *. d0.(5).(i) ) *. (
                                                                                         d22.(i)
                                                                                         -. ( d12.(i) *. d15.(i) /. d0.(5).(i) )
                                                                                         +. 2.0 *. d10.(i) *. d12.(i)
                                                                                       )
  in
  let dt4 i =      1.0 /. ( 4.0 *. d0.(5).(i) *. d0.(5).(i) ) *. (
                                                                   d0.(1).(i) *. d0.(1).(i) 
                                                                   +. exp( -2.0 *. d0.(0).(i) ) *. d0.(3).(i) *. d0.(3).(i)   
                                                                   +. exp( 2.0 *. t ) *. d10.(i) *. d10.(i)
                                                                   +. exp( 2.0 *. ( d0.(0).(i) +. t ) ) *. d12.(i) *. d12.(i)
                                                                 )
                                                                 -. exp( ( d0.(4).(i) +. 2.0 *. d0.(0).(i) -. 3.0 *. t ) /. 2.0 )                             
  in
  let dt5 i =       0.5 *. d0.(5).(i) *. exp( ( d0.(4).(i) +. 2.0 *. d0.(0).(i) -. 3.0 *. t ) /. 2.0 )
  in
  let equations =  [|
    Array.init n ~f:dt0 ;
    Array.init n ~f:dt1 ;
    Array.init n ~f:dt2 ;                                                     
    Array.init n ~f:dt3 ;
    Array.init n ~f:dt4 ;
    Array.init n ~f:dt5
  |] in
  deltat *.> { time = 1.0 ; data = equations }

(*

Does the three CN iterations to generate the increment for the step. arXiv:gr-qc/9909026v1 argues that more than three iterations is no better, so we've hardcoded three.

*)

let cnchangeframe frame deltat deltax accuracy =
  let tempout0 = frame +>> ( changeframe frame deltat deltax accuracy ) in
  let tempdata1 = 0.5 *.> ( frame +>> tempout0 ) in
  let tempout1 = frame +>> ( changeframe tempdata1 deltat deltax accuracy ) in
  let tempdata2 = 0.5 *.> ( frame +>> tempout1 ) in
  changeframe tempdata2 deltat deltax accuracy

(*

Increment a time_frame one step, using CN.

*)

let cnevolveframe frame deltat deltax accuracy =
  frame +>> ( cnchangeframe frame deltat deltax accuracy )

(*

Need functions to load json data.

*)

(*

Take a Yojson.basic list list of numbers, and return it as a float list list.

*)

let filterlist2 jsonlistlist = List.map jsonlistlist ~f:( fun x -> Yojson.Basic.Util.filter_float x ) 

(*

Given one time frame in the json format, ex

{ "time" : 0.0 , "data" : [ [0.1, 0.2, 0.3], [0.11,0.22,0.33]  ]}

return a time_frame equivalent version.

*)

let jsonframetoframe frame = 
  let member a = Yojson.Basic.Util.member a frame in 
  let to_float  = Yojson.Basic.Util.to_float in 
  let to_list  = Yojson.Basic.Util.to_list in 
  let filter_list  = Yojson.Basic.Util.filter_list in 
    {
      time = ( member "time" |> to_float )                                                 ;
      data = ( member "data" |> to_list |> filter_list |> filterlist2 |> listtoarray2 ) 
    }

(*

Next we need a function that takes a time_frame array and produces the json file as output.

*)

(*

Take a float list list and a string and return a Yojson.basic object of
 `Assoc  [ ( "string", `List [ `List [`Float ... ] ; .. ] ) ]

*)

let jsonfloatlist floatlist = List.map floatlist ~f:( fun x -> `Float x ) 

let jsonlist list = `List list 

let jsonlist2float floatlistlist = `List ( List.map floatlistlist ~f:( fun x ->  jsonlist ( jsonfloatlist x ) ) )

let jsonframe frame = 
  let listdata = arraytolist2 frame.data in
    `Assoc
         [ 
          ( "time", `Float frame.time );
          ( "data" , jsonlist2float listdata )
         ]

let jsonwritepretty jsondata path = 
  let message = Yojson.Basic.pretty_to_string jsondata in
  let oc = Out_channel.create path in
  let trash = output_string oc message in
  Out_channel.close oc

type evolution = { frontmatter : (string * Basic.json) list ; timeframes : time_frame array };;

(*

Take a path to a file containing JSON formatted evolution information, and produce the evolution.

*)

let importdataevo path = 
  let member = Yojson.Basic.Util.member  in
  let from_file = Yojson.Basic.from_file  in
  let to_list  = Yojson.Basic.Util.to_list in 
  let jsondata = from_file path in
  let maybeevoisempty inputjson =
    match inputjson with 
      | `Null -> [||]
      | x -> x |> to_list |> List.map  ~f:jsonframetoframe |> List.to_array
  in
  let frames = member "evolution" jsondata |> maybeevoisempty in
  let test input = 
    match input with 
      | ("evolution",_) -> false
      | _ -> true in
  let filteroutevolution = List.filter ~f:test ( Yojson.Basic.Util.to_assoc jsondata ) in
  { frontmatter = filteroutevolution ; timeframes = frames }

(*

Take an evolution and return the Yojson type suitable for printing, preserving the front matter.

*)

let jsonextra evolution =
  let framelist = Array.to_list evolution.timeframes in
  let jsonframelist = List.map framelist ~f:( fun x -> jsonframe x ) in
    `Assoc ( List.append evolution.frontmatter [ ( "evolution", `List jsonframelist ) ] )

(*

Take an evolution with Yojson type Fourier coefficients in the front matter, and return an array array array of each functions sine and cosine coefficients.

*)

let getfourier evolution = 
  let testf input = 
    match input with 
      | ("fourier coefficients",_) -> true
      | _ -> false in 
  let fourier = List.filter ~f:testf evolution.frontmatter in
  let temp = List.nth_exn fourier 0 in
  let test2 shit =
    match shit with
      | (_,x) -> x in
  let json = test2 temp in
  let jsonlist = Yojson.Basic.Util.to_list json in
  let process onefunctionfourier = 
    let list = [ Yojson.Basic.Util.member "sine" onefunctionfourier ; Yojson.Basic.Util.member "cosine" onefunctionfourier ] in
    let list2 = List.map list ~f:Yojson.Basic.Util.to_list in
    List.map list2 ~f:Yojson.Basic.Util.filter_float |> listtoarray2
  in
  Array.of_list ( List.map jsonlist ~f:process )

(*

Take an array of Fourier coefficients for a single function and return the function with those coefficients.

*)

let ffromfourier coefarray =
  let sin x = Pervasives.sin x in
  let cos x = Pervasives.cos x in
  let i2f n = Float.of_int n in
  let sincoefs = coefarray.(0) in
  let coscoefs = coefarray.(1) in
  let sina n x = sincoefs.(n) *. sin( ( i2f( n + 1 ) ) *. x ) in
  let cosa n x = coscoefs.(n) *. cos( ( i2f n        ) *. x ) in
  let sines x   = Array.init ( Array.length sincoefs ) ~f:( fun n -> sina n x ) in
  let cosines x = Array.init ( Array.length coscoefs ) ~f:( fun n -> cosa n x ) in
  ( fun x -> ( arraysum ( sines x ) ) +. ( arraysum ( cosines x ) ) )

(*

Take the nth Fourier coefficients from the front matter of an evolution and return the corresponding function.

*)

let ffromevo evolution n = ( (getfourier evolution).(n) |> ffromfourier ) 

(*

Just extract the initial time from the front matter of an evolution.

*)

let initialtime evolution = 
  let frontmatter = evolution.frontmatter in
  let selector input = 
    match input with
      | ("initial time",x) -> true
      | _ -> false
  in
  let strip input = 
    match input with
      | ("initial time", x ) -> x
      | _ -> `Null
  in
  ( List.nth_exn ( List.filter frontmatter ~f:selector ) 0 ) |> strip |> Yojson.Basic.Util.to_float

(*

Given an evolution with Fourier coefficients in the front matter, return the same data but with the first time_frame added, using the Fourier coefficients to generate it.

*)

let generatefirstframe evolution n =
  let deltax = ( 2.0 *. pi ) /. ( Float.of_int n ) in
  let x j = ( Float.of_int j ) *. deltax in
  let coefs = getfourier evolution in
  let ithfun i = ffromfourier coefs.(i) in
  let numberoffunctions = Array.length coefs in
  match ( evolution.timeframes ) with
    | [||] -> { 
                 frontmatter = evolution.frontmatter ; 
                 timeframes =  [|
                   { 
                      time = initialtime evolution ; 
                      data = Array.init numberoffunctions ~f:( fun i -> Array.init n ~f:( fun j -> ( ithfun i ) ( x j ) ) ) 
                   }
                               |]
              }
    | _ -> evolution

(*

Looks to see if there is a first time frame. If yes, do nothing. If no, generate it from Fourier coefficients with resolution n.

*)

let prepare evolution n =
  match evolution.timeframes with
    | [||] -> generatefirstframe evolution n
    | _ -> evolution

(*

Want functions to calculate the Galileo constraint.

*)

let galconstraint tf = 
  let p   = tf.data.(0) in
  let pip = tf.data.(1) in
  let q   = tf.data.(2) in
  let piq = tf.data.(3) in
  let l   = tf.data.(4) in
  let pil = tf.data.(5) in

  let d data = first_derivative_4th_order ~valuearray:data ~delta:( 2.0 *. pi /. ( Float.of_int ( Array.length p ) ) ) in
  let dp = d p in
  let dq = d q in
  let dl = d l in
  dp *|| pip +|| dq *|| piq +|| dl *|| pil 

(*

This is the main loop. I think the inputs are pretty self-explanatory. The test for the characteristic speed should really be supplied every time, but here we have it as an optional parameter, with the default just returning 1.

*)

let main
  ~inevolution 
  ~timelimit
  ~checkpointfrequency
  ~accuracy
  ?( charspeedtest = ( fun timeframe -> 1.0 ) )
  ~path
  ()
  =

  let evolution = ref ( inevolution ) in (* the ref evolution holds the mutable data to eventually be written, and to which we append the new frames. *)
  let frame = ref ( arraytail( inevolution.timeframes ) ) in (* the ref frame holds the current step's mutable data *)

  let deltax = 2.0 *. pi /. Float.of_int ( Array.length ( (!frame).data.(0) ) ) in (* deltax is the spatial separation computed supposing the domain is the circle with coordinates in 0 to 2pi *)
  let evolveonestep = cnevolveframe in

  let lasttime  = ref (!frame).time  in (* Stores the last time we appended a frame to evolution. *)

  while (  (* Each time through the loop, there are three tests. *)
          ( (!frame).time    < timelimit ) && (* Check that we haven't gone past the explicitly provided limit time. *)
          ( 0.01 > absfloatmax ( galconstraint !frame ) ) && (* Check that the constraint is not too badly satisfied.
                                                                The 0.01 here is a choice that could be made differently. *)
          ( not ( Sys.file_exists_exn "../stop" ) )  (* This is a hack that we use to stop the program prematurely while it's running. *)
        ) do

    let deltat =
      let schemeconstant = 1.0 in                          (* Set the time separation based on the characteristic speed. *)
      let characteristicspeed = charspeedtest !frame in    (* Remember that the function used to compute the             *)
      deltax *. schemeconstant *. characteristicspeed      (* characteristic speed is provided as an argument to main.   *)
    in

    begin
      frame := evolveonestep !frame deltat deltax accuracy ; (* Evolve one step, and update the value of frame. *)
      if (!frame).time   > ( !lasttime +. checkpointfrequency ) then (* If enough time has elapsed since the last time we printed... *)
        begin
          evolution := { frontmatter = (!evolution).frontmatter ; timeframes = Array.append (!evolution).timeframes [| !frame |] } ; (* append a new checkpoint *)
          lasttime := (!frame).time ; (* update the last iterator we checkpointed *)
          jsonwritepretty ( jsonextra !evolution ) path; (* write the data. *)
          print_float ( !lasttime ); (* print the time we're at to STDOUT *)
          print_newline () ; 
        end
    end;

  done ;
  !evolution (* Return the evolution. *)

let main2 inpath =
  let input = importdataevo inpath in

  let test timeframe      = 
    let data = timeframe.data in
    let t =    timeframe.time in
    let pilambda = data.(5) in
    exp( -1.0 *. t ) *. ( Array.fold pilambda ~init:Float.infinity ~f:( fun x y -> Float.min x y ) )
  in

  let output = main
    ~inevolution:input
    ~timelimit:20.01
    ~checkpointfrequency:0.1
    ~accuracy:4 
    ~charspeedtest:test 
    ~path:inpath 
    ()
  in

  let jsonoutput = jsonextra output in
  jsonwritepretty jsonoutput inpath


let command =
  Command.basic
    ~summary:"write tuples of space separated lines"
    Command.Spec.(
      empty
      +> anon ("inpath" %: file) 
    )
    (fun inpath () -> 
       main2 inpath  
    )

let () = Command.run ~version:"1.0" command








