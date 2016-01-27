#light "off"

open System
open System.IO

let debug = true

type address = uint16
type register = uint8
type constant = uint8

type instruction =
	| SysCall of address
	| ClearScreen
	| Return
	| Jump of address
	| Call of address
	| SkipIfEqual of register * constant
	| SkipIfNotEqual of register * constant
	| SkipIfRegistersEqual of register * register
	| SetImmediate of register * constant
	| AddImmediate of register * constant
	| SetRegister of register * register
	| OrRegister of register * register
	| AndRegister of register * register
	| XorRegister of register * register
	| AdcRegister of register * register
	| SwbRegister of register * register
	| ShrRegister of register * register
	| ReverseSwbRegister of register * register
	| ShlRegister of register * register
	| SkipIfRegistersNotEqual of register * register
	| StoreAddress of address
	| JumpOffset of address
	| StoreRandom of register * constant
	| DrawSprite of register * register * constant
	| SkipIfPressed of register
	| SkipIfNotPressed of register
	| SetFromDelay of register
	| WaitKeyPress of register
	| SetToDelay of register
	| SetToSound of register
	| AddAddress of register
	| SetAddressToSprite of register
	| StoreBCD of register
	| StoreRegisters of register
	| LoadRegisters of register

type machineState = {
	ip : int; finished : bool; addr : uint16;
	v0 : uint8; v1 : uint8; v2 : uint8; v3 : uint8;
	v4 : uint8; v5 : uint8; v6 : uint8; v7 : uint8;
	v8 : uint8; v9 : uint8; va : uint8; vb : uint8;
	vc : uint8; vd : uint8; ve : uint8; vf : uint8;
}

type timer = { delayValue : uint8; soundValue : uint8; lastUpdate : DateTime }

let mutable state = {
	ip = 0; finished = false; addr = 0us;
	v0 = 0uy; v1 = 0uy; v2 = 0uy; v3 = 0uy;
	v4 = 0uy; v5 = 0uy; v6 = 0uy; v7 = 0uy;
	v8 = 0uy; v9 = 0uy; va = 0uy; vb = 0uy;
	vc = 0uy; vd = 0uy; ve = 0uy; vf = 0uy;
}

let mem = File.ReadAllBytes ("rom.c8")

let mutable timers = { delayValue = 0uy; soundValue = 0uy; lastUpdate = DateTime.Now }
let updateTimers timers = 
	let now = DateTime.Now in
	let diff = now - timers.lastUpdate in
	if diff.TotalMilliseconds < 16.6 then timers else
	{
		delayValue = if timers.delayValue > 0uy then timers.delayValue - 1uy else 0uy;
		soundValue = if timers.soundValue > 0uy then timers.soundValue - 1uy else 0uy;
		lastUpdate = now
	}

let print x = printfn "%A" x; x

let decode state =
	let addr x y z = ((x |> uint16) <<< 8) ||| ((y |> uint16) <<< 4) ||| ((z |> uint16) <<< 0) in
	let const2 x y = (x <<< 4) ||| y in
	let a = (mem.[state.ip+0] &&& 0xf0uy >>> 8) in
	let b = (mem.[state.ip+0] &&& 0x0fuy >>> 0) in
	let c = (mem.[state.ip+1] &&& 0xf0uy >>> 8) in
	let d = (mem.[state.ip+1] &&& 0x0fuy >>> 0) in
	let inst = match a with
	| 0x0uy when b = 0x0uy && c = 0xeuy && d = 0x0uy -> ClearScreen
	| 0x0uy when b = 0x0uy && c = 0xeuy && d = 0xeuy -> Return
	| 0x0uy -> SysCall(addr b c d)
	| 0x1uy -> Jump(addr b c d)
	| 0x2uy -> Call(addr b c d)
	| 0x3uy -> SkipIfEqual(b, const2 c d)
	| 0x4uy -> SkipIfNotEqual(b, const2 c d)
	| 0x5uy when d = 0x0uy -> SkipIfRegistersEqual(b, c)
	| 0x6uy -> SetImmediate(b, const2 c d)
	| 0x7uy -> AddImmediate(b, const2 c d)
	| 0x8uy when d = 0x0uy -> SetRegister(b, c)
	| 0x8uy when d = 0x1uy -> OrRegister(b, c)
	| 0x8uy when d = 0x2uy -> AndRegister(b, c)
	| 0x8uy when d = 0x3uy -> XorRegister(b, c)
	| 0x8uy when d = 0x4uy -> AdcRegister(b, c)
	| 0x8uy when d = 0x5uy -> SwbRegister(b, c)
	| 0x8uy when d = 0x6uy -> ShrRegister(b, c)
	| 0x8uy when d = 0x7uy -> ReverseSwbRegister(b, c)
	| 0x8uy when d = 0xeuy -> ShlRegister(b, c)
	| 0x9uy when d = 0x0uy -> SkipIfRegistersNotEqual(b, c)
	| 0xauy -> StoreAddress(addr b c d)
	| 0xbuy -> JumpOffset(addr b c d)
	| 0xcuy -> StoreRandom(b, const2 c d)
	| 0xduy -> DrawSprite(b, c, d)
	| 0xeuy when c = 0x9uy && d = 0xeuy -> SkipIfPressed(b)
	| 0xeuy when c = 0xauy && d = 0x1uy -> SkipIfNotPressed(b)
	| 0xfuy when c = 0x0uy && d = 0x7uy -> SetFromDelay(b)
	| 0xfuy when c = 0x0uy && d = 0xauy -> WaitKeyPress(b)
	| 0xfuy when c = 0x1uy && d = 0x5uy -> SetToDelay(b)
	| 0xfuy when c = 0x1uy && d = 0x8uy -> SetToSound(b)
	| 0xfuy when c = 0x1uy && d = 0xeuy -> AddAddress(b)
	| 0xfuy when c = 0x2uy && d = 0x9uy -> SetAddressToSprite(b)
	| 0xfuy when c = 0x3uy && d = 0x3uy -> StoreBCD(b)
	| 0xfuy when c = 0x5uy && d = 0x5uy -> StoreRegisters(b)
	| 0xfuy when c = 0x6uy && d = 0x5uy -> LoadRegisters(b)
	| _ -> failwith <| sprintf "Unknown opcode at %03X: %X%X%X%X" state.ip a b c d
	in
	inst, state

let disassemble x =
	let inst, state = x in
	let label = match inst with
	| ClearScreen -> "CLS"
	| Return -> "RET"
	| SysCall(addr) -> sprintf "SYS %03X" addr
	| Jump(addr) -> sprintf "JP %03X" addr
	| Call(addr) -> sprintf "CALL %03X" addr
	| SkipIfEqual(x,c) -> sprintf "SE V%X, %02X" x c
	| SkipIfNotEqual(x,c) -> sprintf "SNE V%X, %02X" x c
	| SkipIfRegistersEqual(x,y) -> sprintf "SE V%X, V%X" x y
	| SetImmediate(x,c) -> sprintf "LD V%X, %02X" x c
	| AddImmediate(x,c) -> sprintf "ADD V%X, %02X" x c
	| SetRegister(x,y) -> sprintf "LD V%X, V%X" x y
	| OrRegister(x,y) -> sprintf "OR V%X, V%X" x y
	| AndRegister(x,y) -> sprintf "AND V%X, V%X" x y
	| XorRegister(x,y) -> sprintf "XOR V%X, V%X" x y
	| AdcRegister(x,y) -> sprintf "ADD V%X, V%X" x y
	| SwbRegister(x,y) -> sprintf "SUB V%X, V%X" x y
	| ShrRegister(x,y) -> sprintf "SHR V%X, V%X" x y
	| ReverseSwbRegister(x,y) -> sprintf "SUBN V%X, V%X" x y
	| ShlRegister(x,y) -> sprintf "SHL V%X, V%X" x y
	| SkipIfRegistersNotEqual(x,y) -> sprintf "SNE V%X, V%X" x y
	| StoreAddress(addr) -> sprintf "LD I, %03X" addr
	| JumpOffset(addr) -> sprintf "JP V0, %03X" addr
	| StoreRandom(x,c) -> sprintf "RND V%X, %02X" x c
	| DrawSprite(x,y,c) -> sprintf "DRW V%X, V%X, %X" x y c
	| SkipIfPressed(x) -> sprintf "SKP V%X" x
	| SkipIfNotPressed(x) -> sprintf "SKNP V%X" x
	| SetFromDelay(x) -> sprintf "LD V%X, DT" x
	| WaitKeyPress(x) -> sprintf "LD V%X, K" x
	| SetToDelay(x) -> sprintf "LD DT, %X" x
	| SetToSound(x) -> sprintf "LD ST, %X" x
	| AddAddress(x) -> sprintf "ADD I, V%X" x
	| SetAddressToSprite(x) -> sprintf "LD F, V%X" x
	| StoreBCD(x) -> sprintf "LD B, V%X" x
	| StoreRegisters(x) -> sprintf "LD [I], V%X" x
	| LoadRegisters(x) -> sprintf "LD V%X, [I]" x
	in
	printfn "%03X: %s" state.ip label;
	inst, state

let execute x =
	let inst, state = x in
	let get reg = match reg with
		| 0x0uy -> state.v0 | 0x1uy -> state.v1 | 0x2uy -> state.v2 | 0x3uy -> state.v3
		| 0x4uy -> state.v4 | 0x5uy -> state.v5 | 0x6uy -> state.v6 | 0x7uy -> state.v7
		| 0x8uy -> state.v8 | 0x9uy -> state.v9 | 0xauy -> state.va | 0xbuy -> state.vb
		| 0xcuy -> state.vc | 0xduy -> state.vd | 0xeuy -> state.ve | 0xfuy -> state.vf
		| _ -> failwith "invalid register" in
	let set reg value state = match reg with
		| 0x0uy -> { state with v0 = value } | 0x1uy -> { state with v1 = value }
		| 0x2uy -> { state with v2 = value } | 0x3uy -> { state with v3 = value }
		| 0x4uy -> { state with v4 = value } | 0x5uy -> { state with v5 = value }
		| 0x6uy -> { state with v6 = value } | 0x7uy -> { state with v7 = value }
		| 0x8uy -> { state with v8 = value } | 0x9uy -> { state with v9 = value }
		| 0xauy -> { state with va = value } | 0xbuy -> { state with vb = value }
		| 0xcuy -> { state with vc = value } | 0xduy -> { state with vd = value }
		| 0xeuy -> { state with ve = value } | 0xfuy -> { state with vf = value }
		| _ -> failwith "invalid register" in
	let next state = { state with ip = state.ip + 2 } in
	let skip state = { state with ip = state.ip + 4 } in
	let jmp addr state = { state with ip = (addr |> int) } in
	match inst with
	| ClearScreen -> state |> next
	| Return -> state |> next
	| SysCall(addr) -> state |> next
	| Jump(addr) -> state |> jmp addr
	| Call(addr) -> state |> jmp addr
	| SkipIfEqual(x,c) -> if (get x) = c then state |> skip else state |> next
	| SkipIfNotEqual(x,c) -> if (get x) <> c then state |> skip else state |> next
	| SkipIfRegistersEqual(x,y) -> if (get x) = (get y) then state |> skip else state |> next
	| SetImmediate(x,c) -> state |> set x c |> next
	| AddImmediate(x,c) -> state |> set x ((get x) + c) |> next
	| SetRegister(x,y) -> state
	| OrRegister(x,y) -> state
	| AndRegister(x,y) -> state
	| XorRegister(x,y) -> state
	| AdcRegister(x,y) -> state
	| SwbRegister(x,y) -> state
	| ShrRegister(x,y) -> state
	| ReverseSwbRegister(x,y) -> state
	| ShlRegister(x,y) -> state
	| SkipIfRegistersNotEqual(x,y) -> if (get x) <> (get y) then state |> skip else state |> next
	| StoreAddress(addr) -> state
	| JumpOffset(addr) -> state
	| StoreRandom(x,c) -> state
	| DrawSprite(x,y,c) -> state
	| SkipIfPressed(x) -> state
	| SkipIfNotPressed(x) -> state
	| SetFromDelay(x) -> state
	| WaitKeyPress(x) -> state
	| SetToDelay(x) -> state
	| SetToSound(x) -> state
	| AddAddress(x) -> state
	| SetAddressToSprite(x) -> state
	| StoreBCD(x) -> state
	| StoreRegisters(x) -> state
	| LoadRegisters(x) -> state

let run () =
	let disassemble = if debug then disassemble else (fun x -> x) in
	while state.finished <> true do
		timers <- updateTimers timers;
		state <- state |> decode |> disassemble |> execute
	done
do
	run ();
	Console.ReadKey() |> ignore
