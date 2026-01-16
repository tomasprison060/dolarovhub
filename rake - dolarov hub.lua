
local StrToNumber = tonumber;
local Byte = string.byte;
local Char = string.char;
local Sub = string.sub;
local Subg = string.gsub;
local Rep = string.rep;
local Concat = table.concat;
local Insert = table.insert;
local LDExp = math.ldexp;
local GetFEnv = getfenv or function()
	return _ENV;
end;
local Setmetatable = setmetatable;
local PCall = pcall;
local Select = select;
local Unpack = unpack or table.unpack;
local ToNumber = tonumber;
local function VMCall(ByteString, vmenv, ...)
	local DIP = 1;
	local repeatNext;
	ByteString = Subg(Sub(ByteString, 5), "..", function(byte)
		if (Byte(byte, 2) == 81) then
			repeatNext = StrToNumber(Sub(byte, 1, 1));
			return "";
		else
			local a = Char(StrToNumber(byte, 16));
			if repeatNext then
				local b = Rep(a, repeatNext);
				repeatNext = nil;
				return b;
			else
				return a;
			end
		end
	end);
	local function gBit(Bit, Start, End)
		if End then
			local Res = (Bit / (2 ^ (Start - 1))) % (2 ^ (((End - 1) - (Start - 1)) + 1));
			return Res - (Res % 1);
		else
			local Plc = 2 ^ (Start - 1);
			return (((Bit % (Plc + Plc)) >= Plc) and 1) or 0;
		end
	end
	local function gBits8()
		local a = Byte(ByteString, DIP, DIP);
		DIP = DIP + 1;
		return a;
	end
	local function gBits16()
		local a, b = Byte(ByteString, DIP, DIP + 2);
		DIP = DIP + 2;
		return (b * 256) + a;
	end
	local function gBits32()
		local a, b, c, d = Byte(ByteString, DIP, DIP + 3);
		DIP = DIP + 4;
		return (d * 16777216) + (c * 65536) + (b * 256) + a;
	end
	local function gFloat()
		local Left = gBits32();
		local Right = gBits32();
		local IsNormal = 1;
		local Mantissa = (gBit(Right, 1, 20) * (2 ^ 32)) + Left;
		local Exponent = gBit(Right, 21, 31);
		local Sign = ((gBit(Right, 32) == 1) and -1) or 1;
		if (Exponent == 0) then
			if (Mantissa == 0) then
				return Sign * 0;
			else
				Exponent = 1;
				IsNormal = 0;
			end
		elseif (Exponent == 2047) then
			return ((Mantissa == 0) and (Sign * (1 / 0))) or (Sign * NaN);
		end
		return LDExp(Sign, Exponent - 1023) * (IsNormal + (Mantissa / (2 ^ 52)));
	end
	local function gString(Len)
		local Str;
		if not Len then
			Len = gBits32();
			if (Len == 0) then
				return "";
			end
		end
		Str = Sub(ByteString, DIP, (DIP + Len) - 1);
		DIP = DIP + Len;
		local FStr = {};
		for Idx = 1, #Str do
			FStr[Idx] = Char(Byte(Sub(Str, Idx, Idx)));
		end
		return Concat(FStr);
	end
	local gInt = gBits32;
	local _R;
	function v27(...)
		return {...}, Select("#", ...);
	end
	local function Deserialize()
		local Instrs = {};
		local Functions = {};
		local Lines = {};
		local Chunk = {Instrs,Functions,nil,Lines};
		local ConstCount = gBits32();
		local Consts = {};
		for Idx = 1, ConstCount do
			local Type = gBits8();
			local Cons;
			if (Type == 1) then
				Cons = gBits8() ~= 0;
			elseif (Type == 2) then
				Cons = gFloat();
			elseif (Type == 3) then
				Cons = gString();
			end
			Consts[Idx] = Cons;
		end
		Chunk[3] = gBits8();
		for Idx = 1, gBits32() do
			local Descriptor = gBits8();
			if (gBit(Descriptor, 1, 1) == 0) then
				local Type = gBit(Descriptor, 2, 3);
				local Mask = gBit(Descriptor, 4, 6);
				local Inst = {gBits16(),gBits16(),nil,nil};
				if (Type == 0) then
					Inst[3] = gBits16();
					Inst[4] = gBits16();
				elseif (Type == 1) then
					Inst[3] = gBits32();
				elseif (Type == 2) then
					Inst[3] = gBits32() - (2 ^ 16);
				elseif (Type == 3) then
					Inst[3] = gBits32() - (2 ^ 16);
					Inst[4] = gBits16();
				end
				if (gBit(Mask, 1, 1) == 1) then
					Inst[2] = Consts[Inst[2]];
				end
				if (gBit(Mask, 2, 2) == 1) then
					Inst[3] = Consts[Inst[3]];
				end
				if (gBit(Mask, 3, 3) == 1) then
					Inst[4] = Consts[Inst[4]];
				end
				Instrs[Idx] = Inst;
			end
		end
		for Idx = 1, gBits32() do
			Functions[Idx - 1] = Deserialize();
		end
		return Chunk;
	end
	local function Wrap(Chunk, Upvalues, Env)
		local Instr = Chunk[1];
		local Proto = Chunk[2];
		local Params = Chunk[3];
		return function(...)
			local Instr = Instr;
			local Proto = Proto;
			local Params = Params;
			local _R = _R;
			local VIP = 1;
			local Top = -1;
			local Vararg = {};
			local Args = {...};
			local PCount = Select("#", ...) - 1;
			local Lupvals = {};
			local Stk = {};
			for Idx = 0, PCount do
				if (Idx >= Params) then
					Vararg[Idx - Params] = Args[Idx + 1];
				else
					Stk[Idx] = Args[Idx + 1];
				end
			end
			local Varargsz = (PCount - Params) + 1;
			local Inst;
			local Enum;
			while true do
				Inst = Instr[VIP];
				Enum = Inst[1];
				if (Enum <= 68) then
					if (Enum <= 33) then
						if (Enum <= 16) then
							if (Enum <= 7) then
								if (Enum <= 3) then
									if (Enum <= 1) then
										if (Enum > 0) then
											local B;
											local A;
											Stk[Inst[2]] = Env[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											B = Stk[Inst[3]];
											Stk[A + 1] = B;
											Stk[A] = B[Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											B = Stk[Inst[3]];
											Stk[A + 1] = B;
											Stk[A] = B[Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Env[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										else
											local B;
											local A;
											A = Inst[2];
											B = Stk[Inst[3]];
											Stk[A + 1] = B;
											Stk[A] = B[Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Upvalues[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A](Unpack(Stk, A + 1, Inst[3]));
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											B = Stk[Inst[3]];
											Stk[A + 1] = B;
											Stk[A] = B[Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
											VIP = VIP + 1;
											Inst = Instr[VIP];
											if Stk[Inst[2]] then
												VIP = VIP + 1;
											else
												VIP = Inst[3];
											end
										end
									elseif (Enum == 2) then
										local Results;
										local Edx;
										local Results, Limit;
										local B;
										local A;
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Results, Limit = _R(Stk[A](Stk[A + 1]));
										Top = (Limit + A) - 1;
										Edx = 0;
										for Idx = A, Top do
											Edx = Edx + 1;
											Stk[Idx] = Results[Edx];
										end
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Results = {Stk[A](Unpack(Stk, A + 1, Top))};
										Edx = 0;
										for Idx = A, Inst[4] do
											Edx = Edx + 1;
											Stk[Idx] = Results[Edx];
										end
										VIP = VIP + 1;
										Inst = Instr[VIP];
										VIP = Inst[3];
									else
										local A = Inst[2];
										local Cls = {};
										for Idx = 1, #Lupvals do
											local List = Lupvals[Idx];
											for Idz = 0, #List do
												local Upv = List[Idz];
												local NStk = Upv[1];
												local DIP = Upv[2];
												if ((NStk == Stk) and (DIP >= A)) then
													Cls[DIP] = NStk[DIP];
													Upv[1] = Cls;
												end
											end
										end
									end
								elseif (Enum <= 5) then
									if (Enum > 4) then
										local B;
										local A;
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
									else
										local B;
										local A;
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									end
								elseif (Enum == 6) then
									local A;
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
								else
									local B;
									local A;
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Upvalues[Inst[3]] = Stk[Inst[2]];
								end
							elseif (Enum <= 11) then
								if (Enum <= 9) then
									if (Enum > 8) then
										local A;
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										do
											return;
										end
									else
										local Results;
										local Edx;
										local Results, Limit;
										local B;
										local A;
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Results, Limit = _R(Stk[A](Stk[A + 1]));
										Top = (Limit + A) - 1;
										Edx = 0;
										for Idx = A, Top do
											Edx = Edx + 1;
											Stk[Idx] = Results[Edx];
										end
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Results = {Stk[A](Unpack(Stk, A + 1, Top))};
										Edx = 0;
										for Idx = A, Inst[4] do
											Edx = Edx + 1;
											Stk[Idx] = Results[Edx];
										end
										VIP = VIP + 1;
										Inst = Instr[VIP];
										VIP = Inst[3];
									end
								elseif (Enum == 10) then
									Stk[Inst[2]] = Upvalues[Inst[3]];
								else
									local A;
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
								end
							elseif (Enum <= 13) then
								if (Enum == 12) then
									local B;
									local A;
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
								else
									local A = Inst[2];
									local T = Stk[A];
									for Idx = A + 1, Top do
										Insert(T, Stk[Idx]);
									end
								end
							elseif (Enum <= 14) then
								local A = Inst[2];
								Stk[A](Stk[A + 1]);
							elseif (Enum == 15) then
								if (Stk[Inst[2]] == Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								local A;
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								for Idx = Inst[2], Inst[3] do
									Stk[Idx] = nil;
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3] ~= 0;
							end
						elseif (Enum <= 24) then
							if (Enum <= 20) then
								if (Enum <= 18) then
									if (Enum == 17) then
										if (Stk[Inst[2]] <= Inst[4]) then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									else
										local A;
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										do
											return Stk[Inst[2]];
										end
										VIP = VIP + 1;
										Inst = Instr[VIP];
										do
											return;
										end
									end
								elseif (Enum > 19) then
									local B;
									local A;
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3] ~= 0;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								else
									Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
								end
							elseif (Enum <= 22) then
								if (Enum > 21) then
									local B;
									local A;
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
								else
									local B;
									local A;
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
								end
							elseif (Enum == 23) then
								Upvalues[Inst[3]] = Stk[Inst[2]];
							else
								local B;
								local A;
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
							end
						elseif (Enum <= 28) then
							if (Enum <= 26) then
								if (Enum > 25) then
									local A;
									Stk[Inst[2]]();
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									VIP = Inst[3];
								else
									for Idx = Inst[2], Inst[3] do
										Stk[Idx] = nil;
									end
								end
							elseif (Enum == 27) then
								if (Stk[Inst[2]] == Inst[4]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								local B;
								local A;
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
							end
						elseif (Enum <= 30) then
							if (Enum > 29) then
								local T;
								local Edx;
								local Results, Limit;
								local B;
								local A;
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
								Top = (Limit + A) - 1;
								Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								T = Stk[A];
								for Idx = A + 1, Top do
									Insert(T, Stk[Idx]);
								end
							else
								Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
							end
						elseif (Enum <= 31) then
							local A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
						elseif (Enum == 32) then
							local B;
							local A;
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
						else
							local B;
							local A;
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = {};
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = {};
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = {};
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = {};
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = {};
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
						end
					elseif (Enum <= 50) then
						if (Enum <= 41) then
							if (Enum <= 37) then
								if (Enum <= 35) then
									if (Enum > 34) then
										local A = Inst[2];
										local Results = {Stk[A](Stk[A + 1])};
										local Edx = 0;
										for Idx = A, Inst[4] do
											Edx = Edx + 1;
											Stk[Idx] = Results[Edx];
										end
									else
										Stk[Inst[2]] = Wrap(Proto[Inst[3]], nil, Env);
									end
								elseif (Enum == 36) then
									local A;
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
								else
									local B;
									local A;
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
								end
							elseif (Enum <= 39) then
								if (Enum == 38) then
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
								else
									local Results;
									local Edx;
									local Results, Limit;
									local B;
									local A;
									Stk[Inst[2]] = Inst[3] ~= 0;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Upvalues[Inst[3]] = Stk[Inst[2]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results, Limit = _R(Stk[A](Stk[A + 1]));
									Top = (Limit + A) - 1;
									Edx = 0;
									for Idx = A, Top do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results = {Stk[A](Unpack(Stk, A + 1, Top))};
									Edx = 0;
									for Idx = A, Inst[4] do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									VIP = Inst[3];
								end
							elseif (Enum == 40) then
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
							else
								local Results;
								local Edx;
								local Results, Limit;
								local B;
								local A;
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results, Limit = _R(Stk[A](Stk[A + 1]));
								Top = (Limit + A) - 1;
								Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results = {Stk[A](Unpack(Stk, A + 1, Top))};
								Edx = 0;
								for Idx = A, Inst[4] do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								VIP = Inst[3];
							end
						elseif (Enum <= 45) then
							if (Enum <= 43) then
								if (Enum == 42) then
									local Results;
									local Edx;
									local Results, Limit;
									local B;
									local A;
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results, Limit = _R(Stk[A](Stk[A + 1]));
									Top = (Limit + A) - 1;
									Edx = 0;
									for Idx = A, Top do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results = {Stk[A](Unpack(Stk, A + 1, Top))};
									Edx = 0;
									for Idx = A, Inst[4] do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									VIP = Inst[3];
								else
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if (Stk[Inst[2]] == Inst[4]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								end
							elseif (Enum > 44) then
								do
									return;
								end
							else
								local A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
							end
						elseif (Enum <= 47) then
							if (Enum == 46) then
								if Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								local A;
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return Stk[Inst[2]];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							end
						elseif (Enum <= 48) then
							local A;
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							do
								return;
							end
						elseif (Enum == 49) then
							local A = Inst[2];
							local T = Stk[A];
							for Idx = A + 1, Inst[3] do
								Insert(T, Stk[Idx]);
							end
						else
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						end
					elseif (Enum <= 59) then
						if (Enum <= 54) then
							if (Enum <= 52) then
								if (Enum == 51) then
									Stk[Inst[2]] = Inst[3];
								else
									local A;
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return;
									end
								end
							elseif (Enum == 53) then
								local Results;
								local Edx;
								local Results, Limit;
								local B;
								local A;
								Stk[Inst[2]] = Inst[3] ~= 0;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Upvalues[Inst[3]] = Stk[Inst[2]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results, Limit = _R(Stk[A](Stk[A + 1]));
								Top = (Limit + A) - 1;
								Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results = {Stk[A](Unpack(Stk, A + 1, Top))};
								Edx = 0;
								for Idx = A, Inst[4] do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								VIP = Inst[3];
							else
								local B;
								local A;
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							end
						elseif (Enum <= 56) then
							if (Enum > 55) then
								do
									return Stk[Inst[2]];
								end
							else
								local A;
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								do
									return Stk[A](Unpack(Stk, A + 1, Inst[3]));
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								do
									return Unpack(Stk, A, Top);
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							end
						elseif (Enum <= 57) then
							local B;
							local A;
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = {};
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
						elseif (Enum > 58) then
							if not Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						else
							local A;
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							VIP = Inst[3];
						end
					elseif (Enum <= 63) then
						if (Enum <= 61) then
							if (Enum > 60) then
								local A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
							else
								local Edx;
								local Results, Limit;
								local A;
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] * Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
								Top = (Limit + A) - 1;
								Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] * Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if (Stk[Inst[2]] < Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							end
						elseif (Enum > 62) then
							local B = Inst[3];
							local K = Stk[B];
							for Idx = B + 1, Inst[4] do
								K = K .. Stk[Idx];
							end
							Stk[Inst[2]] = K;
						else
							local Results;
							local Edx;
							local Results, Limit;
							local B;
							local A;
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Results, Limit = _R(Stk[A](Stk[A + 1]));
							Top = (Limit + A) - 1;
							Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Results = {Stk[A](Unpack(Stk, A + 1, Top))};
							Edx = 0;
							for Idx = A, Inst[4] do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							VIP = Inst[3];
						end
					elseif (Enum <= 65) then
						if (Enum == 64) then
							local Results;
							local Edx;
							local Results, Limit;
							local A;
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Results, Limit = _R(Stk[A](Stk[A + 1]));
							Top = (Limit + A) - 1;
							Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Results = {Stk[A](Unpack(Stk, A + 1, Top))};
							Edx = 0;
							for Idx = A, Inst[4] do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							VIP = Inst[3];
						else
							Env[Inst[3]] = Stk[Inst[2]];
						end
					elseif (Enum <= 66) then
						local A = Inst[2];
						local C = Inst[4];
						local CB = A + 2;
						local Result = {Stk[A](Stk[A + 1], Stk[CB])};
						for Idx = 1, C do
							Stk[CB + Idx] = Result[Idx];
						end
						local R = Result[1];
						if R then
							Stk[CB] = R;
							VIP = Inst[3];
						else
							VIP = VIP + 1;
						end
					elseif (Enum > 67) then
						local T;
						local B;
						local A;
						Stk[Inst[2]] = Env[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Env[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Env[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						B = Stk[Inst[3]];
						Stk[A + 1] = B;
						Stk[A] = B[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Env[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = {};
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						T = Stk[A];
						B = Inst[3];
						for Idx = 1, B do
							T[Idx] = Stk[A + Idx];
						end
					else
						local B;
						local A;
						A = Inst[2];
						B = Stk[Inst[3]];
						Stk[A + 1] = B;
						Stk[A] = B[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A](Unpack(Stk, A + 1, Inst[3]));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						if Stk[Inst[2]] then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					end
				elseif (Enum <= 103) then
					if (Enum <= 85) then
						if (Enum <= 76) then
							if (Enum <= 72) then
								if (Enum <= 70) then
									if (Enum > 69) then
										local B;
										local A;
										Stk[Inst[2]]();
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]]();
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
									else
										local B;
										local A;
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
									end
								elseif (Enum == 71) then
									local Edx;
									local Results, Limit;
									local B;
									local A;
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
									Top = (Limit + A) - 1;
									Edx = 0;
									for Idx = A, Top do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A]();
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
								else
									local A;
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return;
									end
								end
							elseif (Enum <= 74) then
								if (Enum == 73) then
									if (Inst[2] < Stk[Inst[4]]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								else
									local Edx;
									local Results, Limit;
									local B;
									local A;
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] / Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
									Top = (Limit + A) - 1;
									Edx = 0;
									for Idx = A, Top do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
								end
							elseif (Enum > 75) then
								local Edx;
								local Results;
								local A;
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results = {Stk[A](Stk[A + 1])};
								Edx = 0;
								for Idx = A, Inst[4] do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								VIP = Inst[3];
							else
								local B;
								local A;
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								for Idx = Inst[2], Inst[3] do
									Stk[Idx] = nil;
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
							end
						elseif (Enum <= 80) then
							if (Enum <= 78) then
								if (Enum > 77) then
									local A = Inst[2];
									local Results, Limit = _R(Stk[A](Stk[A + 1]));
									Top = (Limit + A) - 1;
									local Edx = 0;
									for Idx = A, Top do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
								else
									local A = Inst[2];
									local B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
								end
							elseif (Enum == 79) then
								local A;
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
							else
								Stk[Inst[2]] = {};
							end
						elseif (Enum <= 82) then
							if (Enum == 81) then
								local B;
								local A;
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
							else
								Stk[Inst[2]] = Stk[Inst[3]] * Inst[4];
							end
						elseif (Enum <= 83) then
							local B;
							local A;
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = {};
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
						elseif (Enum == 84) then
							Stk[Inst[2]] = Env[Inst[3]];
						else
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if (Stk[Inst[2]] <= Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						end
					elseif (Enum <= 94) then
						if (Enum <= 89) then
							if (Enum <= 87) then
								if (Enum > 86) then
									local B;
									local A;
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] * Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] * Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] * Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
								else
									local T;
									local B;
									local A;
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									T = Stk[A];
									B = Inst[3];
									for Idx = 1, B do
										T[Idx] = Stk[A + Idx];
									end
								end
							elseif (Enum > 88) then
								local A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							else
								VIP = Inst[3];
							end
						elseif (Enum <= 91) then
							if (Enum > 90) then
								local T;
								local B;
								local A;
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								T = Stk[A];
								B = Inst[3];
								for Idx = 1, B do
									T[Idx] = Stk[A + Idx];
								end
							else
								local A = Inst[2];
								Stk[A] = Stk[A]();
							end
						elseif (Enum <= 92) then
							Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
						elseif (Enum > 93) then
							local B;
							local A;
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						else
							local A;
							A = Inst[2];
							Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							VIP = Inst[3];
						end
					elseif (Enum <= 98) then
						if (Enum <= 96) then
							if (Enum == 95) then
								local B;
								local A;
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								VIP = Inst[3];
							else
								local B;
								local A;
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
							end
						elseif (Enum > 97) then
							local B;
							local A;
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						else
							local B;
							local A;
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						end
					elseif (Enum <= 100) then
						if (Enum == 99) then
							local A = Inst[2];
							do
								return Unpack(Stk, A, Top);
							end
						else
							local A;
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							do
								return;
							end
						end
					elseif (Enum <= 101) then
						Stk[Inst[2]] = Stk[Inst[3]] * Stk[Inst[4]];
					elseif (Enum > 102) then
						local A = Inst[2];
						local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
						Top = (Limit + A) - 1;
						local Edx = 0;
						for Idx = A, Top do
							Edx = Edx + 1;
							Stk[Idx] = Results[Edx];
						end
					else
						Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Inst[4];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = {};
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = {};
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = {};
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
					end
				elseif (Enum <= 120) then
					if (Enum <= 111) then
						if (Enum <= 107) then
							if (Enum <= 105) then
								if (Enum > 104) then
									local A = Inst[2];
									local T = Stk[A];
									local B = Inst[3];
									for Idx = 1, B do
										T[Idx] = Stk[A + Idx];
									end
								else
									Stk[Inst[2]] = not Stk[Inst[3]];
								end
							elseif (Enum > 106) then
								Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
							else
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] * Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								VIP = Inst[3];
							end
						elseif (Enum <= 109) then
							if (Enum > 108) then
								local NewProto = Proto[Inst[3]];
								local NewUvals;
								local Indexes = {};
								NewUvals = Setmetatable({}, {__index=function(_, Key)
									local Val = Indexes[Key];
									return Val[1][Val[2]];
								end,__newindex=function(_, Key, Value)
									local Val = Indexes[Key];
									Val[1][Val[2]] = Value;
								end});
								for Idx = 1, Inst[4] do
									VIP = VIP + 1;
									local Mvm = Instr[VIP];
									if (Mvm[1] == 113) then
										Indexes[Idx - 1] = {Stk,Mvm[3]};
									else
										Indexes[Idx - 1] = {Upvalues,Mvm[3]};
									end
									Lupvals[#Lupvals + 1] = Indexes;
								end
								Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
							else
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							end
						elseif (Enum > 110) then
							Stk[Inst[2]]();
						else
							local A = Inst[2];
							do
								return Unpack(Stk, A, A + Inst[3]);
							end
						end
					elseif (Enum <= 115) then
						if (Enum <= 113) then
							if (Enum > 112) then
								Stk[Inst[2]] = Stk[Inst[3]];
							else
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							end
						elseif (Enum == 114) then
							local A = Inst[2];
							local Results = {Stk[A](Unpack(Stk, A + 1, Top))};
							local Edx = 0;
							for Idx = A, Inst[4] do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						else
							local A = Inst[2];
							local Results, Limit = _R(Stk[A]());
							Top = (Limit + A) - 1;
							local Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						end
					elseif (Enum <= 117) then
						if (Enum == 116) then
							local K;
							local B;
							local A;
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = {};
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							B = Inst[3];
							K = Stk[B];
							for Idx = B + 1, Inst[4] do
								K = K .. Stk[Idx];
							end
							Stk[Inst[2]] = K;
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							B = Inst[3];
							K = Stk[B];
							for Idx = B + 1, Inst[4] do
								K = K .. Stk[Idx];
							end
							Stk[Inst[2]] = K;
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						else
							local B;
							local A;
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						end
					elseif (Enum <= 118) then
						local B;
						local A;
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Env[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						B = Stk[Inst[3]];
						Stk[A + 1] = B;
						Stk[A] = B[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						if Stk[Inst[2]] then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					elseif (Enum == 119) then
						if (Stk[Inst[2]] < Stk[Inst[4]]) then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					else
						local B;
						local A;
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						B = Stk[Inst[3]];
						Stk[A + 1] = B;
						Stk[A] = B[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						if Stk[Inst[2]] then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					end
				elseif (Enum <= 129) then
					if (Enum <= 124) then
						if (Enum <= 122) then
							if (Enum == 121) then
								local B;
								local A;
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							else
								Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
							end
						elseif (Enum > 123) then
							local B;
							local A;
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = {};
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
						else
							local B;
							local A;
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if not Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						end
					elseif (Enum <= 126) then
						if (Enum > 125) then
							local B;
							local A;
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							B = Stk[Inst[4]];
							if B then
								VIP = VIP + 1;
							else
								Stk[Inst[2]] = B;
								VIP = Inst[3];
							end
						else
							Stk[Inst[2]][Inst[3]] = Inst[4];
						end
					elseif (Enum <= 127) then
						local A;
						A = Inst[2];
						Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Env[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A](Unpack(Stk, A + 1, Inst[3]));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						VIP = Inst[3];
					elseif (Enum == 128) then
						local Results;
						local Edx;
						local Results, Limit;
						local B;
						local A;
						Stk[Inst[2]] = Inst[3] ~= 0;
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Upvalues[Inst[3]] = Stk[Inst[2]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Env[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Env[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						B = Stk[Inst[3]];
						Stk[A + 1] = B;
						Stk[A] = B[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Results, Limit = _R(Stk[A](Stk[A + 1]));
						Top = (Limit + A) - 1;
						Edx = 0;
						for Idx = A, Top do
							Edx = Edx + 1;
							Stk[Idx] = Results[Edx];
						end
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Results = {Stk[A](Unpack(Stk, A + 1, Top))};
						Edx = 0;
						for Idx = A, Inst[4] do
							Edx = Edx + 1;
							Stk[Idx] = Results[Edx];
						end
						VIP = VIP + 1;
						Inst = Instr[VIP];
						VIP = Inst[3];
					elseif (Stk[Inst[2]] <= Stk[Inst[4]]) then
						VIP = VIP + 1;
					else
						VIP = Inst[3];
					end
				elseif (Enum <= 133) then
					if (Enum <= 131) then
						if (Enum > 130) then
							Stk[Inst[2]] = Inst[3] ~= 0;
							VIP = VIP + 1;
						else
							local B;
							local A;
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						end
					elseif (Enum > 132) then
						Stk[Inst[2]] = Stk[Inst[3]] / Stk[Inst[4]];
					else
						Stk[Inst[2]] = Inst[3] ~= 0;
					end
				elseif (Enum <= 135) then
					if (Enum == 134) then
						local A;
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A](Unpack(Stk, A + 1, Inst[3]));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Env[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A] = Stk[A](Stk[A + 1]);
						VIP = VIP + 1;
						Inst = Instr[VIP];
						if Stk[Inst[2]] then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					else
						local B;
						local A;
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						B = Stk[Inst[3]];
						Stk[A + 1] = B;
						Stk[A] = B[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						if Stk[Inst[2]] then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					end
				elseif (Enum <= 136) then
					Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
					VIP = VIP + 1;
					Inst = Instr[VIP];
					Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
					VIP = VIP + 1;
					Inst = Instr[VIP];
					Stk[Inst[2]] = Upvalues[Inst[3]];
					VIP = VIP + 1;
					Inst = Instr[VIP];
					Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
					VIP = VIP + 1;
					Inst = Instr[VIP];
					Stk[Inst[2]] = Upvalues[Inst[3]];
					VIP = VIP + 1;
					Inst = Instr[VIP];
					Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
					VIP = VIP + 1;
					Inst = Instr[VIP];
					Stk[Inst[2]] = Stk[Inst[3]] * Stk[Inst[4]];
					VIP = VIP + 1;
					Inst = Instr[VIP];
					Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
				elseif (Enum == 137) then
					local B = Stk[Inst[4]];
					if B then
						VIP = VIP + 1;
					else
						Stk[Inst[2]] = B;
						VIP = Inst[3];
					end
				else
					local A = Inst[2];
					do
						return Stk[A](Unpack(Stk, A + 1, Inst[3]));
					end
				end
				VIP = VIP + 1;
			end
		end;
	end
	return Wrap(Deserialize(), {}, vmenv)(...);
end
return VMCall("LOL!8F3Q00030A3Q006C6F6164737472696E6703043Q0067616D6503073Q00482Q7470476574031C3Q00682Q7470733A2Q2F7369726975732E6D656E752F7261796669656C64030C3Q0043726561746557696E646F7703043Q004E616D65030A3Q00627920646F6C61726F7603043Q0049636F6E028Q00030C3Q004C6F6164696E675469746C6503073Q006C6F6164696E67030F3Q004C6F6164696E675375627469746C6503053Q005468656D6503073Q0044656661756C7403163Q0044697361626C655261796669656C6450726F6D707473010003143Q0044697361626C654275696C645761726E696E677303133Q00436F6E66696775726174696F6E536176696E6703073Q00456E61626C6564030A3Q00466F6C6465724E616D650003083Q0046696C654E616D65030B3Q00646F6C61726F762068756203073Q00446973636F726403063Q00496E76697465030C3Q006E6F696E766974656C696E6B030D3Q0052656D656D6265724A6F696E7303093Q004B657953797374656D030B3Q004B657953652Q74696E677303053Q005469746C6503083Q00556E7469746C656403083Q005375627469746C65030A3Q004B65792053797374656D03043Q004E6F7465032A3Q004E6F206D6574686F64206F66206F627461696E696E6720746865206B65792069732070726F76696465642Q033Q004B657903073Q00536176654B65792Q01030F3Q00477261624B657946726F6D5369746503053Q0048652Q6C6F03093Q0043726561746554616203043Q004D61696E022Q00A0E9AAB3F04103043Q004D697363030D3Q0043726561746553656374696F6E030A3Q004765745365727669636503083Q004C69676874696E67030A3Q0052756E5365727669636503073Q00506C617965727303113Q005265706C69636174656453746F72616765030F3Q00444554454354494F4E5F52414E4745026Q00494003103Q004D494E5F52554E5F44495354414E4345026Q00344003103Q004D41585F52554E5F44495354414E4345026Q00444003103Q0053502Q45445F4D554C5449504C494552027Q004003103Q004D494E5F5550444154455F44454C4159027B14AE47E17A843F03103Q004D41585F5550444154455F44454C4159029A5Q99A93F03103Q0044495354414E43455F5343414C494E47026Q006940030B3Q00434C4F53455F52414E4745026Q00244003103Q00534D2Q4F54484E452Q535F434C4F5345030E3Q00534D2Q4F54484E452Q535F464152029A5Q99B93F030A3Q005241595F484549474854026Q00144003093Q005241595F4445505448026Q0024C003133Q00414C5445524E41544956455F4F2Q465345545303073Q00566563746F72332Q033Q006E6577026Q0014C003083Q006973416374697665030B3Q00636F2Q6E656374696F6E7303113Q006F726967696E616C57616C6B53702Q6564030A3Q0074617267657450617274030C3Q00437265617465546F2Q676C65030F3Q00416E74692D52616B65204368617365030C3Q0043752Q72656E7456616C756503043Q00466C616703083Q00416E746952616B6503083Q0043612Q6C6261636B030F3Q00437265617465506172616772617068030D3Q00486F7720697420776F726B733F03073Q00436F6E74656E7403713Q0057692Q6C206465746563742072616B652C20616E64206175746F2072756E20617761792066726F6D206974206E6F206D612Q74657220776861742E204C696B6520612062612Q726965722C20616C736F20626C6F636B7320796F752066726F6D206170726F78696D6174696E672068696D03273Q004D616B652068696D20436861736520796F7520286D6574686F6420312C2077692Q6C20446965292Q033Q0045535003153Q004578706572696D656E74616C204175746F6661726D03603Q0053696D706C652E2054686520706C617965722077692Q6C20616C776179732062652072752Q6E696E6720696E20746865206F2Q706F7369746520646972656374696F6E206F66207468652072616B652C206E6F206D612Q74657220776861742E030C3Q0043726561746542752Q746F6E03123Q0044656C6574652066612Q6C2064616D616765031B3Q0044656C65746520496E7374616D696E612028496E66696E6974652903093Q00455350205374752Q66030B3Q004C6F63616C506C6179657203093Q0046692Q6C436F6C6F7203063Q00436F6C6F723303073Q0066726F6D524742025Q00806140025Q00E06F4003103Q0046692Q6C5472616E73706172656E6379026Q66E63F030C3Q004F75746C696E65436F6C6F72026Q00544003133Q004F75746C696E655472616E73706172656E637903043Q0052616B65026Q00E03F026Q00594003083Q00466C61726547756E026Q33D33F03093Q0053752Q706C79426F78025Q00806640030A3Q00486967686C6967687473030B3Q00436F2Q6E656374696F6E73030F3Q00437265617465486967686C69676874030F3Q0052656D6F7665486967686C6967687403123Q00436C65616E7570436F2Q6E656374696F6E73030E3Q005365747570506C61796572455350030E3Q0053657475704F626A656374455350030E3Q00466C61726547756E5069636B557003093Q00466C6172652047756E030E3Q0053752Q706C7920626F782045535003043Q006245535003093Q0053637261702045535003043Q007345535003083Q00547261702045535003043Q0074455350030F3Q0046752Q6C204272696768746E652Q7303133Q00456E61626C6520546869726420506572736F6E026Q00F03F03153Q00456E61626C652053702Q65642028434672616D652903103Q00546F2Q676C654C6F63616C53702Q6564030C3Q00437265617465536C6964657203103Q0053702Q6564204D756C7469706C69657203053Q0052616E6765026Q00104003093Q00496E6372656D656E74030F3Q00536C6964657253702Q65644D756C7400B2012Q0012473Q00013Q00122Q000100023Q00202Q00010001000300122Q000300046Q000100039Q0000026Q0001000200202Q00013Q00054Q00033Q000B00302Q00030006000700307D00030008000900306C0003000A000B00302Q0003000C000700302Q0003000D000E00302Q0003000F001000302Q0003001100104Q00043Q000300302Q00040013001000302Q00040014001500302Q00040016001700102Q0003001200042Q005000043Q000300302800040013001000302Q00040019001A00302Q0004001B001000102Q00030018000400302Q0003001C00104Q00043Q000700302Q0004001E001F00302Q00040020002100302Q00040022002300302Q00040016002400307D00040025002600307D0004002700102Q0050000500013Q001233000600284Q006900050001000100107000040024000500101E0003001D00044Q00010003000200202Q00020001002900122Q0004002A3Q00122Q0005002B6Q00020005000200202Q00030001002900122Q0005002C3Q00122Q0006002B6Q00030006000200202Q00040002002D00122Q000600176Q00040006000100122Q000400023Q00202Q00040004002E00122Q0006002F6Q00040006000200122Q000500023Q00202Q00050005002E00122Q000700306Q00050007000200122Q000600023Q00202Q00060006002E00122Q000800316Q00060008000200122Q000700023Q00202Q00070007002E00122Q000900326Q0007000900024Q00083Q000D00302Q00080033003400302Q00080035003600302Q00080037003800302Q00080039003A00302Q0008003B003C00302Q0008003D003E00302Q0008003F004000302Q00080041004200302Q00080043003E00302Q00080044004500302Q00080046004700302Q0008004800494Q000900033Q00122Q000A004B3Q00202Q000A000A004C00122Q000B00473Q00122Q000C00093Q00122Q000D00476Q000A000D000200122Q000B004B3Q00202Q000B000B004C00122Q000C004D3Q00122Q000D00093Q00122Q000E00476Q000B000E000200122Q000C004B3Q00202Q000C000C004C00122Q000D00473Q00122Q000E00093Q00122Q000F004D6Q000C000F000200122Q000D004B3Q00202Q000D000D004C00122Q000E004D3Q00122Q000F00093Q00122Q0010004D6Q000D00106Q00093Q00010010700008004A00092Q002600093Q000400302Q0009004E00104Q000A5Q00102Q0009004F000A00302Q00090050001500302Q00090051001500066D000A3Q000100012Q00713Q00093Q00066D000B0001000100012Q00713Q00083Q00066D000C0002000100012Q00713Q00093Q00066D000D0003000100032Q00713Q00094Q00713Q00084Q00713Q000B3Q00066D000E0004000100022Q00713Q000C4Q00713Q00093Q00066D000F0005000100082Q00713Q00094Q00713Q00064Q00713Q00084Q00713Q000C4Q00713Q000E4Q00713Q00054Q00713Q000D4Q00713Q000A4Q008400106Q0019001100113Q00066D00120006000100022Q00713Q00114Q00713Q00103Q00066D00130007000100012Q00713Q00103Q00201C0014000200524Q00163Q000400302Q00160006005300302Q00160054001000302Q00160055005600066D00170008000100012Q00713Q000F3Q00107C0016005700174Q00140016000200202Q0015000200584Q00173Q000200302Q0017001E005900307D0017005A005B2Q005900150017000200201C0016000200524Q00183Q000400302Q00180006005C00302Q00180054001000302Q00180055005D000222001900093Q0010700018005700192Q00590016001800022Q008400176Q0019001800183Q00066D0019000A000100012Q00713Q00173Q00066D001A000B000100032Q00713Q00174Q00713Q00184Q00713Q00193Q00201C001B000200524Q001D3Q000400302Q001D0006005E00302Q001D0054001000302Q001D0055005D00066D001E000C000100012Q00713Q001A3Q00107C001D0057001E4Q001B001D000200202Q001C000200584Q001E3Q000200302Q001E001E005900307D001E005A005F2Q0059001C001E000200204D001D000200602Q0050001F3Q000200307D001F0006006100066D0020000D000100012Q00713Q00073Q00107C001F005700204Q001D001F000200202Q001E000200604Q00203Q000200302Q00200006006200066D0021000E000100012Q00713Q00073Q0010210020005700214Q001E0020000200202Q001F0002002D00122Q002100636Q001F0021000100202Q001F000600644Q00203Q00044Q00213Q000500302Q00210013001000122Q002200663Q00202Q00220022006700122Q002300093Q00122Q002400683Q00122Q002500696Q00220025000200102Q00210065002200302Q0021006A006B00122Q002200663Q00202Q00220022006700122Q002300093Q00122Q0024006D3Q00122Q002500696Q00220025000200102Q0021006C002200302Q0021006E000900102Q0020003100214Q00213Q000500302Q00210013001000122Q002200663Q00202Q00220022006700122Q002300693Q00122Q002400093Q00122Q002500096Q00220025000200102Q00210065002200302Q0021006A007000122Q002200663Q00202Q00220022006700122Q002300693Q00122Q002400713Q00122Q002500096Q00220025000200102Q0021006C002200302Q0021006E000900102Q0020006F00214Q00213Q000500302Q00210013001000122Q002200663Q00202Q00220022006700122Q002300693Q00122Q002400403Q00122Q002500096Q00220025000200102Q00210065002200302Q0021006A007300122Q002200663Q00202Q00220022006700122Q002300693Q00122Q002400713Q00122Q002500096Q00220025000200102Q0021006C002200302Q0021006E000900102Q0020007200214Q00213Q000500302Q00210013001000122Q002200663Q00202Q00220022006700122Q002300093Q00122Q002400693Q00122Q002500096Q00220025000200102Q00210065002200302Q0021006A007000122Q002200663Q00202Q00220022006700122Q002300093Q00122Q002400753Q00122Q002500096Q0022002500020010660021006C002200302Q0021006E000900102Q0020007400214Q00213Q00024Q00225Q00102Q0021007600224Q00225Q00102Q0021007700220002220022000F3Q001070002100780022000222002200103Q001070002100790022000222002200113Q0010700021007A002200066D00220012000100032Q00713Q001F4Q00713Q00204Q00713Q00063Q0010700021007B002200066D00220013000100022Q00713Q00204Q00713Q00053Q0010700021007C002200066D00220014000100012Q00713Q00103Q00066D00230015000100012Q00713Q00103Q00066D00240016000100012Q00713Q00103Q00066D00250017000100012Q00713Q00103Q00200C00260021007B4Q00260002000100202Q00260021007C00122Q0028006F3Q00122Q0029006F6Q00260029000100202Q00260021007C00122Q0028007D3Q00122Q002900726Q00260029000100066D00260018000100032Q00713Q00204Q00713Q00064Q00713Q00214Q0006002700266Q002800023Q00122Q002900313Q00122Q002A00316Q0027002A00014Q002700266Q002800023Q00122Q0029006F3Q00122Q002A006F6Q0027002A00012Q0071002700264Q0005002800023Q00122Q0029007E3Q00122Q002A00726Q0027002A000100202Q0027000200524Q00293Q000400302Q00290006007F00302Q00290054001000302Q00290055008000066D002A0019000100032Q00713Q00104Q00713Q00224Q00713Q00233Q00105300290057002A4Q00270029000200202Q0028000200524Q002A3Q000400302Q002A0006008100302Q002A0054001000302Q002A0055008200066D002B001A000100032Q00713Q00104Q00713Q00124Q00713Q00133Q001053002A0057002B4Q0028002A000200202Q0029000200524Q002B3Q000400302Q002B0006008300302Q002B0054001000302Q002B0055008400066D002C001B000100032Q00713Q00104Q00713Q00244Q00713Q00253Q001070002B0057002C2Q00590029002B00022Q0084002A6Q0019002B002B3Q00066D002C001C000100042Q00713Q002A4Q00713Q002B4Q00713Q00044Q00713Q00053Q00201C002D000300524Q002F3Q000400302Q002F0006008500302Q002F0054001000302Q002F0055005D00066D0030001D000100012Q00713Q002C3Q001053002F005700304Q002D002F000200202Q002E000300524Q00303Q000400302Q00300006008600302Q00300054001000302Q00300055005D0002220031001E3Q002Q100030005700314Q002E003000024Q002F002F3Q00122Q003000876Q00315Q00066D0032001F000100052Q00713Q002F4Q00713Q00304Q00713Q00314Q00713Q00064Q00713Q00053Q00201C0033000300524Q00353Q000400302Q00350006008800302Q00350054001000302Q00350055008900066D00360020000100042Q00713Q00314Q00713Q00324Q00713Q00304Q00713Q002F3Q00105B0035005700364Q00330035000100202Q00330003008A4Q00353Q000600302Q00350006008B4Q003600023Q00122Q003700873Q00122Q0038008D6Q0036000200010010700035008C003600307D0035008E004500307D00350054008700307D00350055008F00066D00360021000100032Q00713Q00304Q00713Q00314Q00713Q00323Q0010700035005700362Q001F0033003500012Q002D3Q00013Q00223Q00053Q0003063Q00697061697273030B3Q00636F2Q6E656374696F6E73030A3Q00446973636F2Q6E65637403053Q007461626C6503053Q00636C656172000F3Q00124C3Q00016Q00015Q00202Q0001000100026Q0002000200044Q0007000100204D0005000400032Q000E0005000200010006423Q0005000100020004583Q000500010012543Q00043Q0020485Q00054Q00015Q00202Q0001000100026Q000200016Q00017Q000C3Q0003073Q00566563746F72332Q033Q006E6577028Q00030A3Q005241595F48454947485403093Q005241595F444550544803093Q00776F726B7370616365031B3Q0046696E64506172744F6E5261795769746849676E6F72654C6973742Q033Q0052617903093Q0043686172616374657203063Q0069706169727303133Q00414C5445524E41544956455F4F2Q4653455453027Q004002443Q001244000200013Q00202Q00020002000200122Q000300036Q00045Q00202Q00040004000400122Q000500036Q0002000500024Q00023Q000200122Q000300013Q00202Q00030003000200122Q000400036Q00055Q00202Q00050005000500122Q000600036Q00030006000200122Q000400063Q00202Q00040004000700122Q000600083Q00202Q0006000600024Q000700026Q000800036Q0006000800024Q000700013Q00202Q0008000100094Q0007000100012Q005900040007000200063B0004001D000100010004583Q001D00012Q00383Q00023Q0012540005000A4Q000A00065Q00203200060006000B2Q00230005000200070004583Q003900012Q005C000A3Q0009001256000B00013Q00202Q000B000B000200122Q000C00036Q000D5Q00202Q000D000D000400122Q000E00036Q000B000E00024Q000B000A000B00122Q000C00063Q00202Q000C000C000700122Q000E00083Q00202Q000E000E00024Q000F000B6Q001000036Q000E001000024Q000F00013Q00202Q0010000100094Q000F000100012Q0059000C000F000200063B000C0039000100010004583Q003900012Q0038000A00023Q00064200050022000100020004583Q00220001001254000500013Q00201200050005000200122Q000600033Q00122Q0007000C3Q00122Q000800036Q0005000800024Q00053Q00054Q000500028Q00017Q00063Q0003093Q00776F726B7370616365030E3Q0046696E6446697273744368696C6403043Q0052616B65030A3Q007461726765745061727403103Q0048756D616E6F6964522Q6F74506172742Q00133Q00127E3Q00013Q00206Q000200122Q000200038Q000200024Q00015Q00062Q0002000A00013Q0004583Q000A000100204D00023Q0002001233000400054Q00590002000400020010700001000400022Q000A00015Q00203200010001000400261B00010010000100060004583Q001000012Q008300016Q0084000100014Q0038000100024Q002D3Q00017Q00223Q0003093Q00436861726163746572030E3Q0046696E6446697273744368696C6403103Q0048756D616E6F6964522Q6F745061727403153Q0046696E6446697273744368696C644F66436C612Q7303083Q0048756D616E6F696403083Q0053656174506172742Q033Q00536974010003043Q007461736B03043Q0077616974022D431CEBE2361A3F030A3Q0074617267657450617274030E3Q00497344657363656E64616E744F6603093Q00776F726B737061636503083Q00506F736974696F6E03093Q004D61676E6974756465030F3Q00444554454354494F4E5F52414E474503043Q006D6174682Q033Q006D696E03103Q004D41585F52554E5F44495354414E43452Q033Q006D617803103Q004D494E5F52554E5F44495354414E4345026Q00E83F03043Q00556E697403063Q00434672616D652Q033Q006E6577030B3Q00434C4F53455F52414E474503103Q00534D2Q4F54484E452Q535F434C4F5345030E3Q00534D2Q4F54484E452Q535F46415203043Q004C65727003063Q004D6F7665546F03103Q004D494E5F5550444154455F44454C415903103Q004D41585F5550444154455F44454C415903103Q0044495354414E43455F5343414C494E47016A3Q00203200013Q000100063B00010004000100010004583Q000400012Q002D3Q00013Q00204D000200010002001275000400036Q00020004000200202Q00030001000400122Q000500056Q00030005000200062Q0002000E00013Q0004583Q000E000100063B0003000F000100010004583Q000F00012Q002D3Q00013Q00203200040003000600062E0004001700013Q0004583Q0017000100307D000300070008001254000400093Q00203200040004000A0012330005000B4Q000E0004000200012Q000A00045Q00203200040004000C00062E0004002200013Q0004583Q002200012Q000A00045Q00207B00040004000C00202Q00040004000D00122Q0006000E6Q00040006000200062Q00040023000100010004583Q002300012Q002D3Q00014Q000A00045Q00205500040004000C00202Q00040004000F00202Q00050002000F4Q00060004000500202Q0006000600104Q000700013Q00202Q00070007001100062Q00060069000100070004583Q00690001001254000700123Q00203C0007000700134Q000800013Q00202Q00080008001400122Q000900123Q00202Q0009000900154Q000A00013Q00202Q000A000A001600202Q000B000600174Q0009000B6Q00073Q00024Q00080005000400202Q0008000800184Q0009000800074Q0009000500094Q000A00026Q000B00096Q000C8Q000A000C000200122Q000B00193Q00202Q000B000B001A4Q000C000A6Q000D00046Q000B000D00024Q000C00013Q00202Q000C000C001B00062Q0006004D0001000C0004583Q004D00012Q000A000C00013Q002032000C000C001C00063B000C004F000100010004583Q004F00012Q000A000C00013Q002032000C000C001D002032000D0002001900204A000D000D001E4Q000F000B6Q0010000C6Q000D0010000200102Q00020019000D00202Q000D0003001F4Q000F000A6Q000D000F000100122Q000D00123Q00202Q000D000D00154Q000E00013Q00202Q000E000E002000122Q000F00123Q00202Q000F000F00134Q001000013Q00202Q0010001000214Q001100013Q00202Q0011001100224Q0011000600114Q000F00116Q000D3Q000200122Q000E00093Q00202Q000E000E000A4Q000F000D6Q000E000200012Q002D3Q00017Q00073Q0003093Q00776F726B7370616365030A3Q004368696C64412Q64656403073Q00436F2Q6E65637403053Q007461626C6503063Q00696E73657274030B3Q00636F2Q6E656374696F6E73030C3Q004368696C6452656D6F76656400193Q0012543Q00013Q0020325Q000200204D5Q000300066D00023Q000100012Q000A8Q00203Q0002000200122Q000100043Q00202Q0001000100054Q000200013Q00202Q0002000200064Q00038Q00010003000100122Q000100013Q00202Q00010001000700202Q00010001000300066D00030001000100012Q000A3Q00014Q006400010003000100122Q000100043Q00202Q0001000100054Q000200013Q00202Q0002000200064Q00038Q0001000300016Q00013Q00023Q00043Q0003043Q004E616D6503043Q0052616B6503043Q007461736B03043Q007761697401093Q00203200013Q000100261B00010008000100020004583Q00080001001254000100033Q0020320001000100042Q006F0001000100012Q000A00016Q006F0001000100012Q002D3Q00017Q00043Q0003043Q004E616D6503043Q0052616B65030A3Q00746172676574506172740001063Q00203200013Q000100261B00010005000100020004583Q000500012Q000A00015Q00307D0001000300042Q002D3Q00017Q000D3Q0003083Q006973416374697665030B3Q004C6F63616C506C6179657203093Q0043686172616374657203153Q0046696E6446697273744368696C644F66436C612Q7303083Q0048756D616E6F696403113Q006F726967696E616C57616C6B53702Q656403093Q0057616C6B53702Q656403103Q0053502Q45445F4D554C5449504C49455203093Q0048656172746265617403073Q00436F2Q6E65637403053Q007461626C6503063Q00696E73657274030B3Q00636F2Q6E656374696F6E7301434Q000A00015Q00203200010001000100060F0001000500013Q0004583Q000500012Q002D3Q00014Q000A00015Q001070000100014Q000A000100013Q00203200010001000200062E3Q003000013Q0004583Q0030000100203200020001000300062E0002001200013Q0004583Q0012000100203200020001000300204D000200020004001233000400054Q005900020004000200062E0002001D00013Q0004583Q001D00012Q000A00035Q00208800040002000700102Q0003000600044Q00035Q00202Q0003000300064Q000400023Q00202Q0004000400084Q00030003000400102Q0002000700032Q000A000300034Q00460003000100014Q000300046Q0003000100014Q000300053Q00202Q00030003000900202Q00030003000A00066D00053Q000100032Q000A8Q000A3Q00064Q00713Q00014Q007F00030005000200122Q0004000B3Q00202Q00040004000C4Q00055Q00202Q00050005000D4Q000600036Q00040006000100044Q004200012Q000A000200074Q006F00020001000100203200020001000300062E0002003900013Q0004583Q0039000100203200020001000300204D000200020004001233000400054Q005900020004000200062E0002004200013Q0004583Q004200012Q000A00035Q00203200030003000600062E0003004200013Q0004583Q004200012Q000A00035Q0020320003000300060010700002000700032Q002D3Q00013Q00013Q00013Q0003083Q00697341637469766500084Q000A7Q0020325Q000100062E3Q000700013Q0004583Q000700012Q000A3Q00014Q000A000100024Q000E3Q000200012Q002D3Q00017Q00063Q0003093Q00776F726B7370616365030C3Q0057616974466F724368696C6403063Q0046696C746572030B3Q005363726170537061776E7303043Q007461736B03053Q00737061776E000F3Q0012043Q00013Q00206Q000200122Q000200038Q0002000200206Q000200122Q000200048Q0002000200122Q000100053Q00202Q00010001000600066D00023Q000100022Q000A3Q00014Q00718Q003D0001000200022Q001700016Q002D3Q00013Q00013Q001D3Q0003063Q00697061697273030E3Q0047657444657363656E64616E74732Q033Q0049734103083Q00426173655061727403043Q004E616D6503053Q006D6174636803053Q005363726170030E3Q0046696E6446697273744368696C6403073Q005363726170484C03083Q00496E7374616E63652Q033Q006E657703093Q00486967686C6967687403073Q0041646F726E2Q6503063Q00506172656E7403093Q0046692Q6C436F6C6F7203063Q00436F6C6F723303073Q0066726F6D524742025Q00E06F40025Q00805640026Q004E40030C3Q004F75746C696E65436F6C6F72026Q00594003103Q0046692Q6C5472616E73706172656E637902CD5QCCDC3F03133Q004F75746C696E655472616E73706172656E6379029A5Q99B93F03043Q007461736B03043Q0077616974026Q000840003C4Q000A7Q00062E3Q003B00013Q0004583Q003B00010012543Q00014Q0008000100013Q00202Q0001000100024Q000100029Q00000200044Q003400012Q000A00055Q00063B0005000D000100010004583Q000D00010004583Q0036000100204D000500040003001233000700044Q005900050007000200062E0005003400013Q0004583Q0034000100203200050004000500204D000500050006001233000700074Q005900050007000200062E0005003400013Q0004583Q0034000100204D000500040008001233000700094Q005900050007000200063B00050034000100010004583Q003400010012540005000A3Q00200B00050005000B00122Q0006000C6Q00050002000200302Q00050005000900102Q0005000D000400102Q0005000E000400122Q000600103Q00202Q00060006001100122Q000700123Q00122Q000800133Q00122Q000900146Q00060009000200102Q0005000F000600122Q000600103Q00202Q00060006001100122Q000700123Q00122Q000800123Q00122Q000900166Q00060009000200102Q00050015000600302Q00050017001800302Q00050019001A0006423Q0009000100020004583Q000900010012543Q001B3Q0020325Q001C0012330001001D4Q000E3Q000200010004585Q00012Q002D3Q00017Q00083Q0003063Q0069706169727303093Q00776F726B7370616365030E3Q0047657444657363656E64616E74732Q033Q0049734103093Q00486967686C6967687403043Q004E616D6503073Q005363726170484C03073Q0044657374726F7900154Q00359Q007Q00124Q00013Q00122Q000100023Q00202Q0001000100034Q000100029Q00000200044Q0012000100204D000500040004001233000700054Q005900050007000200062E0005001200013Q0004583Q0012000100203200050004000600261B00050012000100070004583Q0012000100204D0005000400082Q000E0005000200010006423Q0008000100020004583Q000800012Q002D3Q00019Q002Q0001044Q000A00016Q007100026Q000E0001000200012Q002D3Q00019Q002Q002Q014Q002D3Q00017Q00143Q0003093Q0043686172616374657203153Q0046696E6446697273744368696C644F66436C612Q7303083Q0048756D616E6F6964030E3Q0046696E6446697273744368696C6403103Q0048756D616E6F6964522Q6F745061727403083Q0053656174506172742Q033Q00536974010003043Q007461736B03043Q0077616974029A5Q99B93F030E3Q00497344657363656E64616E744F6603093Q00776F726B737061636503083Q00506F736974696F6E03043Q00556E6974027Q004003063Q00434672616D6503043Q007761726E03363Q00546172676574207061727420646F6573206E6F74206578697374206F72206973206E6F7420696E2074686520776F726B73706163652103303Q00537065616B657220636861726163746572206F722048756D616E6F6964522Q6F7450617274206E6F7420666F756E642102403Q00203200023Q000100062E0002000600013Q0004583Q0006000100204D000300020002001233000500034Q00590003000500022Q000A00035Q00062E0003003F00013Q0004583Q003F000100203200033Q000100062E0003003700013Q0004583Q0037000100203200033Q000100204D000300030004001233000500054Q005900030005000200062E0003003700013Q0004583Q0037000100203200033Q000100207800030003000500202Q00043Q000100202Q00040004000200122Q000600036Q00040006000200062Q0004002200013Q0004583Q0022000100203200050004000600062E0005002200013Q0004583Q0022000100307D000400070008001254000500093Q00203200050005000A0012330006000B4Q000E00050002000100062E0001003300013Q0004583Q0033000100204D00050001000C0012540007000D4Q005900050007000200062E0005003300013Q0004583Q0033000100203200050001000E00206A00060003000E4Q00070006000500202Q00070007000F00122Q000800103Q00202Q0009000300114Q000A000700084Q00090009000A00102Q00030011000900044Q003A0001001254000500123Q001233000600134Q000E0005000200010004583Q003A0001001254000300123Q001233000400144Q000E000300020001001254000300093Q00203200030003000A0012330004000B4Q000E0003000200010004583Q000600012Q002D3Q00017Q00093Q0003043Q0067616D6503073Q00506C6179657273030B3Q004C6F63616C506C6179657203093Q00776F726B7370616365030E3Q0046696E6446697273744368696C6403043Q0052616B6503103Q0048756D616E6F6964522Q6F745061727403043Q007761726E032E3Q0052616B65206E6F7420666F756E6420696E20776F726B73706163652E2057692Q6C20737461792072752Q6E696E67011F4Q00178Q000A00015Q00062E0001001E00013Q0004583Q001E0001001254000100013Q00207600010001000200202Q00010001000300122Q000200043Q00202Q00020002000500122Q000400066Q00020004000200062Q0002001200013Q0004583Q00120001001254000200043Q00203200020002000600204D000200020005001233000400074Q00590002000400022Q0017000200014Q000A000200013Q00062E0002001B00013Q0004583Q001B00012Q000A000200024Q0071000300014Q000A000400014Q001F0002000400010004583Q001E0001001254000200083Q001233000300094Q000E0002000200012Q002D3Q00019Q002Q0001044Q000A00016Q007100026Q000E0001000200012Q002D3Q00017Q00063Q00030C3Q0057616974466F724368696C6403083Q0046445F4576656E7403073Q0044657374726F7903053Q007072696E7403343Q0053752Q63652Q7366752Q6C792064656C657465642046445F4576656E742066726F6D205265706C69636174656453746F72616765033B3Q0046445F4576656E74206E6F7420666F756E6420696E205265706C69636174656453746F726167652E2Q20436F756C64206E6F742064656C6574652E00104Q00827Q00206Q000100122Q000200028Q0002000200064Q000C00013Q0004583Q000C000100204D00013Q00032Q005D00010002000100122Q000100043Q00122Q000200056Q00010002000100044Q000F0001001254000100043Q001233000200064Q000E0001000200012Q002D3Q00017Q00103Q00030E3Q0046696E6446697273744368696C6403063Q00544B534D4E4103053Q004576656E7403063Q00697061697273030E3Q00676574636F2Q6E656374696F6E7303093Q00436F2Q6E6563746564030A3Q00446973636F2Q6E65637403103Q006765746C6F616465646D6F64756C657303043Q004E616D652Q033Q004D5F4803053Q007461626C6503063Q00696E7365727403073Q0072657175697265030B3Q0054616B655374616D696E6103043Q007761726E034D3Q004D5F48206D6F64756C6520646F6573206E6F74206861766520612054616B655374616D696E612066756E6374696F6E206F7220697320696E636F2Q726563746C7920737472756374757265642E00464Q00507Q00066D00013Q000100012Q00718Q008200025Q00202Q00020002000100122Q000400026Q00020004000200062Q0002002000013Q0004583Q002000012Q000A00025Q00208700020002000200202Q00020002000100122Q000400036Q00020004000200062Q0002002000013Q0004583Q002000012Q000A00025Q00204000020002000200202Q00020002000300122Q000300043Q00122Q000400056Q000500026Q000400056Q00033Q000500044Q001E000100203200080007000600062E0008001E00013Q0004583Q001E000100204D0008000700072Q000E00080002000100064200030019000100020004583Q00190001001254000200043Q001254000300084Q0073000300014Q007200023Q00040004583Q0043000100203200070006000900261B000700430001000A0004583Q004300012Q0071000700014Q0071000800064Q003D00070002000200063B00070043000100010004583Q004300010012540007000B3Q00208600070007000C4Q00088Q000900066Q00070009000100122Q0007000D6Q000800066Q00070002000200062Q0007004000013Q0004583Q0040000100203200080007000E00062E0008004000013Q0004583Q0040000100203200080007000E00066D00090001000100012Q00713Q00083Q0010700007000E00092Q000300085Q0004583Q004300010012540008000F3Q001233000900104Q000E00080002000100064200020025000100020004583Q002500012Q002D3Q00013Q00023Q00013Q0003063Q00697061697273010D3Q001254000100014Q000A00026Q00230001000200030004583Q0008000100060F0005000800013Q0004583Q000800012Q0084000600014Q0038000600023Q00064200010004000100020004583Q000400012Q008400016Q0038000100024Q002D3Q00017Q00023Q00028Q00026Q00E0BF020D3Q000E4900010007000100010004583Q000700012Q000A00026Q007100035Q001233000400024Q008A000200044Q006300026Q000A00026Q003700038Q000400016Q000200046Q00029Q0000017Q000D3Q00030F3Q0052656D6F7665486967686C6967687403083Q00496E7374616E63652Q033Q006E657703093Q00486967686C6967687403043Q004E616D65030C3Q00455350486967686C6967687403073Q0041646F726E2Q6503093Q0046692Q6C436F6C6F7203103Q0046692Q6C5472616E73706172656E6379030C3Q004F75746C696E65436F6C6F7203133Q004F75746C696E655472616E73706172656E637903063Q00506172656E74030A3Q00486967686C696768747303193Q00063B00010003000100010004583Q000300012Q002D3Q00013Q00204D00033Q00012Q002F000500016Q00030005000100122Q000300023Q00202Q00030003000300122Q000400046Q00030002000200302Q00030005000600102Q00030007000100202Q00040002000800102Q00030008000400202Q00040002000900102Q00030009000400202Q00040002000A00102Q0003000A000400202Q00040002000B00102Q0003000B000400102Q0003000C000100202Q00043Q000D4Q0004000100034Q000300028Q00017Q00033Q00030A3Q00486967686C696768747303073Q0044657374726F790002093Q00203200023Q00012Q001D00020002000100062E0002000800013Q0004583Q0008000100204D0003000200022Q000E00030002000100203200033Q00010020130003000100032Q002D3Q00017Q00033Q0003053Q007061697273030B3Q00436F2Q6E656374696F6E73030A3Q00446973636F2Q6E656374010D3Q001254000100013Q00203200023Q00022Q00230001000200030004583Q0008000100062E0005000800013Q0004583Q0008000100204D0006000500032Q000E00060002000100064200010004000100020004583Q000400012Q005000015Q0010703Q000200012Q002D3Q00017Q00083Q0003063Q00697061697273030A3Q00476574506C6179657273030B3Q00506C61796572412Q64656403073Q00436F2Q6E65637403053Q007461626C6503063Q00696E73657274030B3Q00436F2Q6E656374696F6E73030E3Q00506C6179657252656D6F76696E6701253Q00066D00013Q000100032Q000A8Q000A3Q00014Q00717Q001229000200016Q000300023Q00202Q0003000300024Q000300046Q00023Q000400044Q000D00012Q0071000700014Q0071000800064Q000E0007000200010006420002000A000100020004583Q000A00012Q000A000200023Q00201500020002000300202Q0002000200044Q000400016Q00020004000200122Q000300053Q00202Q00030003000600202Q00043Q00074Q000500026Q0003000500014Q000300023Q00202Q00030003000800202Q00030003000400066D00050001000100012Q00718Q003000030005000200122Q000400053Q00202Q00040004000600202Q00053Q00074Q000600036Q0004000600016Q00013Q00023Q00063Q0003093Q00436861726163746572030E3Q00436861726163746572412Q64656403073Q00436F2Q6E65637403053Q007461626C6503063Q00696E73657274030B3Q00436F2Q6E656374696F6E73011A3Q00062E3Q000500013Q0004583Q000500012Q000A00015Q00060F3Q0006000100010004583Q000600012Q002D3Q00013Q00066D00013Q000100022Q000A3Q00014Q000A3Q00023Q00203200023Q000100062E0002000F00013Q0004583Q000F00012Q0071000200013Q00203200033Q00012Q000E00020002000100203200023Q00020020360002000200034Q000400016Q00020004000200122Q000300043Q00202Q0003000300054Q000400023Q00202Q0004000400064Q000500026Q0003000500016Q00013Q00013Q00083Q0003073Q00506C617965727303073Q00456E61626C6564030F3Q00437265617465486967686C69676874030E3Q0046696E6446697273744368696C6403083Q0048756D616E6F696403043Q004469656403073Q00436F2Q6E656374030F3Q0052656D6F7665486967686C6967687401233Q00063B3Q0003000100010004583Q000300012Q002D3Q00014Q000A00015Q00203200010001000100203200010001000200062E0001001E00013Q0004583Q001E00012Q000A000100013Q00202Q0001000100034Q00038Q00045Q00202Q0004000400014Q00010004000100202Q00013Q000400122Q000300056Q00010003000200062Q0001002200013Q0004583Q002200012Q0019000200023Q00203200030001000600204D00030003000700066D00053Q000100032Q000A3Q00014Q00718Q00713Q00024Q00590003000500022Q0071000200034Q000300025Q0004583Q002200012Q000A000100013Q00204D0001000100082Q007100036Q001F0001000300012Q002D3Q00013Q00013Q00023Q00030F3Q0052656D6F7665486967686C69676874030A3Q00446973636F2Q6E656374000B4Q005E7Q00206Q00014Q000200018Q000200016Q00023Q00064Q000A00013Q0004583Q000A00012Q000A3Q00023Q00204D5Q00022Q000E3Q000200012Q002D3Q00017Q00023Q0003093Q00436861726163746572030F3Q0052656D6F7665486967686C6967687401083Q00203200013Q000100062E0001000700013Q0004583Q000700012Q000A00015Q00204D00010001000200203200033Q00012Q001F0001000300012Q002D3Q00017Q00053Q0003093Q0048656172746265617403073Q00436F2Q6E65637403053Q007461626C6503063Q00696E73657274030B3Q00436F2Q6E656374696F6E7303113Q00066D00033Q000100042Q00713Q00014Q000A8Q00713Q00024Q00718Q000A000400013Q00203200040004000100204D00040004000200066D00060001000100012Q00713Q00034Q003000040006000200122Q000500033Q00202Q00050005000400202Q00063Q00054Q000700046Q0005000700016Q00013Q00023Q00073Q0003093Q00776F726B7370616365030E3Q0046696E6446697273744368696C6403073Q00456E61626C6564030F3Q00437265617465486967686C69676874030F3Q00416E6365737472794368616E67656403073Q00436F2Q6E656374030F3Q0052656D6F7665486967686C6967687400243Q0012143Q00013Q00206Q00024Q00028Q000300018Q0003000200064Q002300013Q0004583Q002300012Q000A000100014Q000A000200024Q001D00010001000200203200010001000300062E0001001F00013Q0004583Q001F00012Q000A000100033Q00204B0001000100044Q00038Q000400016Q000500026Q0004000400054Q0001000400014Q000100013Q00202Q00023Q000500202Q00020002000600066D00043Q000100032Q000A3Q00034Q00718Q00713Q00014Q00590002000400022Q0071000100024Q000300015Q0004583Q002300012Q000A000100033Q00204D0001000100072Q007100036Q001F0001000300012Q002D3Q00013Q00013Q00023Q00030F3Q0052656D6F7665486967686C69676874030A3Q00446973636F2Q6E656374020D3Q00063B0001000C000100010004583Q000C00012Q000A00025Q0020430002000200014Q000400016Q0002000400014Q000200023Q00062Q0002000C00013Q0004583Q000C00012Q000A000200023Q00204D0002000200022Q000E0002000200012Q002D3Q00019Q003Q00034Q000A8Q006F3Q000100012Q002D3Q00017Q00073Q0003093Q00776F726B7370616365030C3Q0057616974466F724368696C6403063Q00446562726973030C3Q0053752Q706C7943726174657303093Q00426F7854687265616403043Q007461736B03053Q00737061776E000F3Q0012043Q00013Q00206Q000200122Q000200038Q0002000200206Q000200122Q000200048Q0002000200122Q000100063Q00202Q00010001000700066D00023Q000100022Q000A8Q00718Q003D000100020002001241000100054Q002D3Q00013Q00013Q001A3Q0003063Q00697061697273030E3Q0047657444657363656E64616E747303043Q004E616D6503053Q006D617463682Q033Q00426F78030E3Q0046696E6446697273744368696C6403053Q00426F78484C03083Q00496E7374616E63652Q033Q006E657703093Q00486967686C6967687403073Q0041646F726E2Q6503063Q00506172656E7403093Q0046692Q6C436F6C6F7203063Q00436F6C6F723303073Q0066726F6D524742026Q002840025Q00A06E40025Q00805240030C3Q004F75746C696E65436F6C6F7203103Q0046692Q6C5472616E73706172656E637902CD5QCCDC3F03133Q004F75746C696E655472616E73706172656E6379029A5Q99B93F03043Q007461736B03043Q0077616974026Q00084000374Q000A7Q00062E3Q003600013Q0004583Q003600010012543Q00014Q0008000100013Q00202Q0001000100024Q000100029Q00000200044Q002F00012Q000A00055Q00063B0005000D000100010004583Q000D00010004583Q0031000100203200050004000300204D000500050004001233000700054Q005900050007000200062E0005002F00013Q0004583Q002F000100204D000500040006001233000700074Q005900050007000200063B0005002F000100010004583Q002F0001001254000500083Q00200B00050005000900122Q0006000A6Q00050002000200302Q00050003000700102Q0005000B000400102Q0005000C000400122Q0006000E3Q00202Q00060006000F00122Q000700103Q00122Q000800113Q00122Q000900126Q00060009000200102Q0005000D000600122Q0006000E3Q00202Q00060006000F00122Q000700103Q00122Q000800113Q00122Q000900126Q00060009000200102Q00050013000600302Q00050014001500302Q0005001600170006423Q0009000100020004583Q000900010012543Q00183Q0020325Q00190012330001001A4Q000E3Q000200010004585Q00012Q002D3Q00017Q00083Q0003063Q0069706169727303093Q00776F726B7370616365030E3Q0047657444657363656E64616E74732Q033Q0049734103093Q00486967686C6967687403043Q004E616D6503053Q00426F78484C03073Q0044657374726F7900154Q00359Q007Q00124Q00013Q00122Q000100023Q00202Q0001000100034Q000100029Q00000200044Q0012000100204D000500040004001233000700054Q005900050007000200062E0005001200013Q0004583Q0012000100203200050004000600261B00050012000100070004583Q0012000100204D0005000400082Q000E0005000200010006423Q0008000100020004583Q000800012Q002D3Q00017Q00073Q0003093Q00776F726B7370616365030C3Q0057616974466F724368696C6403063Q0044656272697303053Q00547261707303093Q00426F7854687265616403043Q007461736B03053Q00737061776E000F3Q0012043Q00013Q00206Q000200122Q000200038Q0002000200206Q000200122Q000200048Q0002000200122Q000100063Q00202Q00010001000700066D00023Q000100022Q000A8Q00718Q003D000100020002001241000100054Q002D3Q00013Q00013Q001A3Q0003063Q00697061697273030E3Q0047657444657363656E64616E747303043Q004E616D6503053Q006D61746368030D3Q0052616B65547261704D6F64656C030E3Q0046696E6446697273744368696C6403063Q0054726170484C03083Q00496E7374616E63652Q033Q006E657703093Q00486967686C6967687403073Q0041646F726E2Q6503063Q00506172656E7403093Q0046692Q6C436F6C6F7203063Q00436F6C6F723303073Q0066726F6D524742025Q00806F40026Q004140026Q001440030C3Q004F75746C696E65436F6C6F7203103Q0046692Q6C5472616E73706172656E637902CD5QCCDC3F03133Q004F75746C696E655472616E73706172656E6379029A5Q99B93F03043Q007461736B03043Q0077616974026Q00084000374Q000A7Q00062E3Q003600013Q0004583Q003600010012543Q00014Q0008000100013Q00202Q0001000100024Q000100029Q00000200044Q002F00012Q000A00055Q00063B0005000D000100010004583Q000D00010004583Q0031000100203200050004000300204D000500050004001233000700054Q005900050007000200062E0005002F00013Q0004583Q002F000100204D000500040006001233000700074Q005900050007000200063B0005002F000100010004583Q002F0001001254000500083Q00200B00050005000900122Q0006000A6Q00050002000200302Q00050003000700102Q0005000B000400102Q0005000C000400122Q0006000E3Q00202Q00060006000F00122Q000700103Q00122Q000800113Q00122Q000900126Q00060009000200102Q0005000D000600122Q0006000E3Q00202Q00060006000F00122Q000700103Q00122Q000800113Q00122Q000900126Q00060009000200102Q00050013000600302Q00050014001500302Q0005001600170006423Q0009000100020004583Q000900010012543Q00183Q0020325Q00190012330001001A4Q000E3Q000200010004585Q00012Q002D3Q00017Q00083Q0003063Q0069706169727303093Q00776F726B7370616365030E3Q0047657444657363656E64616E74732Q033Q0049734103093Q00486967686C6967687403043Q004E616D6503063Q0054726170484C03073Q0044657374726F7900154Q00359Q007Q00124Q00013Q00122Q000100023Q00202Q0001000100034Q000100029Q00000200044Q0012000100204D000500040004001233000700054Q005900050007000200062E0005001200013Q0004583Q0012000100203200050004000600261B00050012000100070004583Q0012000100204D0005000400082Q000E0005000200010006423Q0008000100020004583Q000800012Q002D3Q00017Q00083Q00030C3Q00437265617465546F2Q676C6503043Q004E616D6503043Q0045535020030C3Q0043752Q72656E7456616C756503073Q00456E61626C656403043Q00466C616703043Q004553505F03083Q0043612Q6C6261636B03173Q00207400033Q00014Q00053Q000400122Q000600036Q000700016Q00060006000700102Q0005000200064Q00068Q00060006000200202Q00060006000500102Q00050004000600122Q000600076Q000700026Q00060006000700102Q00050006000600066D00063Q000100042Q000A8Q00713Q00024Q000A3Q00014Q000A3Q00023Q0010700005000800062Q008A000300054Q006300036Q002D3Q00013Q00013Q00073Q0003073Q00456E61626C656403073Q00506C617965727303063Q00697061697273030A3Q00476574506C617965727303093Q00436861726163746572030F3Q00437265617465486967686C69676874030F3Q0052656D6F7665486967686C6967687401204Q002B00018Q000200016Q00010001000200102Q000100016Q000100013Q00262Q0001001F000100020004583Q001F0001001254000100034Q0008000200023Q00202Q0002000200044Q000200036Q00013Q000300044Q001D000100203200060005000500062E0006001D00013Q0004583Q001D000100062E3Q001900013Q0004583Q001900012Q000A000600033Q00205F00060006000600202Q0008000500054Q00095Q00202Q0009000900024Q00060009000100044Q001D00012Q000A000600033Q00204D0006000600070020320008000500052Q001F0006000800010006420001000D000100020004583Q000D00012Q002D3Q00019Q002Q0001094Q00177Q00062E3Q000600013Q0004583Q000600012Q000A000100014Q006F0001000100010004583Q000800012Q000A000100024Q006F0001000100012Q002D3Q00019Q002Q0001094Q00177Q00062E3Q000600013Q0004583Q000600012Q000A000100014Q006F0001000100010004583Q000800012Q000A000100024Q006F0001000100012Q002D3Q00019Q002Q0001094Q00177Q00062E3Q000600013Q0004583Q000600012Q000A000100014Q006F0001000100010004583Q000800012Q000A000100024Q006F0001000100012Q002D3Q00017Q000F3Q00030A3Q00446973636F2Q6E656374030A3Q004272696768746E652Q73026Q00F03F03093Q00436C6F636B54696D65026Q00284003063Q00466F67456E64025Q00408F40030D3Q00476C6F62616C536861646F77732Q01030E3Q004F7574642Q6F72416D6269656E7403063Q00436F6C6F723303073Q0066726F6D524742025Q00A06A40030D3Q0052656E6465725374652Q70656403073Q00436F2Q6E65637400284Q000A7Q00062E3Q001C00013Q0004583Q001C00012Q000A3Q00013Q00062E3Q000B00013Q0004583Q000B00012Q000A3Q00013Q00204D5Q00012Q000E3Q000200012Q00198Q00173Q00014Q000A3Q00023Q00303A3Q000200036Q00023Q00304Q000400056Q00023Q00304Q000600076Q00023Q00304Q000800096Q00023Q00122Q0001000B3Q00202Q00010001000C00122Q0002000D3Q00122Q0003000D3Q00122Q0004000D6Q00010004000200104Q000A000100044Q0024000100066D5Q000100012Q000A3Q00024Q0007000100033Q00202Q00010001000E00202Q00010001000F4Q00038Q0001000300024Q000100014Q000A8Q00688Q00178Q002D3Q00013Q00013Q000C3Q00030A3Q004272696768746E652Q73027Q004003093Q00436C6F636B54696D65026Q002C4003063Q00466F67456E64025Q006AF840030D3Q00476C6F62616C536861646F77730100030E3Q004F7574642Q6F72416D6269656E7403063Q00436F6C6F723303073Q0066726F6D524742026Q00604000114Q00347Q00304Q000100029Q0000304Q000300049Q0000304Q000500069Q0000304Q000700089Q0000122Q0001000A3Q00202Q00010001000B00122Q0002000C3Q00122Q0003000C3Q00122Q0004000C6Q00010004000200104Q000900016Q00019Q002Q0001044Q000A00016Q007100026Q000E0001000200012Q002D3Q00017Q00093Q0003073Q0067657467656E7603053Q007374752Q6603043Q0067616D65030A3Q004765745365727669636503073Q00506C6179657273030B3Q004C6F63616C506C6179657203043Q007461736B03043Q0077616974029A5Q99B93F01143Q001279000100016Q00010001000200102Q000100023Q00122Q000100033Q00202Q00010001000400122Q000300056Q00010003000200202Q00010001000600066D00023Q000100012Q00713Q00014Q0071000300024Q006F0003000100012Q0071000300024Q001A00030001000100122Q000300073Q00202Q00030003000800122Q000400096Q00030002000100044Q000C00012Q002D3Q00013Q00013Q00063Q0003073Q0067657467656E7603053Q007374752Q6603153Q0043616D6572614D61785A2Q6F6D44697374616E6365026Q003E4003153Q0043616D6572614D696E5A2Q6F6D44697374616E6365026Q00E03F000F3Q0012543Q00014Q005A3Q000100020020325Q000200062E3Q000A00013Q0004583Q000A00012Q000A7Q00307D3Q000300042Q000A7Q00307D3Q000500060004583Q000E00012Q000A7Q00307D3Q000300062Q000A7Q00307D3Q000500062Q002D3Q00017Q000B3Q00030A3Q00446973636F2Q6E656374028Q00030B3Q004C6F63616C506C6179657203093Q00436861726163746572030E3Q00436861726163746572412Q64656403043Q0057616974030C3Q0057616974466F724368696C6403083Q0048756D616E6F6964026Q00144003093Q0048656172746265617403073Q00436F2Q6E656374012A4Q000A00015Q00062E0001000800013Q0004583Q000800012Q000A00015Q00204D0001000100012Q000E0001000200012Q0019000100014Q001700016Q00173Q00014Q000A000100023Q00062E0001000E00013Q0004583Q000E00010026113Q000F000100020004583Q000F00012Q002D3Q00014Q000A000100033Q00203200010001000300203200020001000400063B00020017000100010004583Q0017000100203200020001000500204D0002000200062Q003D00020002000200204D000300020007001233000500083Q001233000600094Q005900030006000200063B0003001E000100010004583Q001E00012Q002D3Q00014Q000A000400043Q00203200040004000A00204D00040004000B00066D00063Q000100052Q00713Q00014Q00713Q00024Q00713Q00034Q000A8Q00718Q00590004000600022Q001700046Q002D3Q00013Q00013Q00083Q0003093Q0043686172616374657203063Q00506172656E74030A3Q00446973636F2Q6E656374030D3Q004D6F7665446972656374696F6E03093Q004D61676E6974756465028Q00030B3Q005472616E736C6174654279026Q00244001244Q000A00015Q0020320001000100012Q000A000200013Q00060F0001000C000100020004583Q000C00012Q000A000100023Q00062E0001000C00013Q0004583Q000C00012Q000A000100023Q00203200010001000200063B00010015000100010004583Q001500012Q000A000100033Q00062E0001001200013Q0004583Q001200012Q000A000100033Q00204D0001000100032Q000E0001000200012Q0019000100014Q0017000100034Q002D3Q00014Q000A000100023Q002032000100010004002032000100010005000E4900060023000100010004583Q002300012Q000A000100023Q0020570001000100044Q000200013Q00202Q0002000200074Q000400046Q00040001000400202Q0004000400084Q000400046Q0002000400012Q002D3Q00017Q00013Q00030A3Q00446973636F2Q6E65637401104Q00177Q00062E3Q000700013Q0004583Q000700012Q000A000100014Q000A000200024Q000E0001000200010004583Q000F00012Q000A000100033Q00062E0001000F00013Q0004583Q000F00012Q000A000100033Q00204D0001000100012Q000E0001000200012Q0019000100014Q0017000100034Q002D3Q00019Q002Q0001084Q00178Q000A000100013Q00062E0001000700013Q0004583Q000700012Q000A000100024Q007100026Q000E0001000200012Q002D3Q00017Q00", GetFEnv(), ...);
