structure LongInt =
struct

exception TooLarge of string

local 
 open Word8 
in
(* datatype for long integers; the msb of the head of the list is the sign *) 
 datatype longint = LONGINT of word list

(* function for minimizing the representation of an integer value;
   necessary for implementing CCITT X.209, the Basic Encoding Rules for
   the Abstract Syntax Notation One (ASN.1);				
   the first octet is unnecessary if all of its bits and the most 
   significant bit of the second octet are equal			*)

 fun minimize (LONGINT ws) = 
 let (* returns true if the 7th bit is one 				*)
     fun test7thBit byte = (andb(fromInt 128,byte) = fromInt 128)
     fun min (whole as first::second::xs) =
	     if ((first = fromInt 255) andalso (test7thBit second)) 
		orelse
		((first = fromInt 0) andalso not (test7thBit second))
		then min (second::xs)
		else whole
       | min xs = xs
  in LONGINT (min ws)
 end

(* functions for converting to and from the basic numeric datatypes of
   the Basis Library							*)
 fun byteListFromWord32 w =
 let fun curriedWord32andb u v = Word32.andb(u,v)
     val Word8FromWord32Lsb = 
	 fromInt o Word32.toInt o (curriedWord32andb(Word32.fromInt 255)) 
     fun sr bits w32 = Word32.>>(w32,Word.fromInt bits)  
  in map Word8FromWord32Lsb [sr 24 w,sr 16 w,sr 8 w,w]
 end

 fun fromLargeInt num = minimize 
	(LONGINT ((byteListFromWord32 o Word32.fromLargeInt) num))

 fun fromWord32 w = minimize 
	(LONGINT (0wx00 :: (byteListFromWord32 w)) )
	(* 0wx00 is needed when the Msb is 1 - otherwise it 
	   would be considered as a negative number		*)

(*
 fun toWord32 (LONGINT (ws as w8::w8s)) = 
     if let open Int in (List.length ws) > 5 end 
	then raise TooLarge "Cannot convert more than 4 bytes to Word32"
	else 
	let fun word32FromWord8List ([],w) = w
	      | word32FromWord8List ((b::bs),w) = 
		word32FromWord8List 
		(bs, Word32.orb(Word32.<<(w,Word.fromInt 8),
				(Word32.fromInt o Word8.toInt) b))
	 in word32FromWord8List (w8s,(Word32.fromInt 0))
	end
*)

fun toWord32 (LONGINT (ws as w8::w8s)) =
    if let open Int in (List.length ws) > 5 end
       then raise TooLarge "Cannot convert more than 4 bytes to Word32"
       else let val shiftLeft8andOr =
		fn (w8,w32) =>
			Word32.orb(Word32.<<(w32,0wx08),
                	(Word32.fromLargeWord o Word8.toLargeWord) w8)
	     in foldl shiftLeft8andOr 0wx00 ws
	    end
       
(*
fun woWord32 (LONGINT ws) =
    if let open Int in (List.length ws) >4 end
       then raise TooLarge "Cannot convert more than 4 bytes to LargeInt"
       else
*) 

end (* local *)
end (* LongInt *)
