structure Mib = 
struct

 exception NotImplemented of string
 exception BadEncoding of string
 exception Err of string

 datatype inttype =	NAME_AND_NUMBER_LIST of (string*int) list |
			SUBTYPE_SPEC of (int*int) |
			SIMPLE

 datatype mibtype =	BASIC of basictype | 
			SEQUENCE_T of (string*basictype) list |
			SEQUENCEOF_T of mibtype | REF of string 

      and basictype =	INT_T of inttype | 
			OCTETSTRING_T |
			NULL_T 		| 
			OBJ_ID_T 	| 
			NETWORK_ADDRESS_T | 
			IP_ADDRESS_T 	| 
			COUNTER_T 	| 
			GAUGE_T | 
			TIMETICKS_T | 
			DISPLAYSTRING_T of (int*int) option |
			PHYS_ADDRESS_T

 datatype accesstype = READONLY | READWRITE | WRITEONLY | NOTACCESSIBLE

 datatype statustype = MANDATORY | OPTIONAL | OBSOLETE | DEPRECATED

 type rawobject = 	{name:string,
			syntax:mibtype,
			access:accesstype,
			status:statustype,
			descr:string option,
			index:mibtype list,
			objid:string * int}

 type object = 		{name:string,
			syntaxname:string,
			syntax:mibtype,
			access:accesstype,
			status:statustype,
			indextypes:(string * mibtype) list,
			descr:string option}
			
 datatype assignment =	VALUE of string * string * int |
			TYPE of (string*mibtype) |
			OBJECT of rawobject

 type symboltable =	(string * mibtype) list

 type objid = 		int list

 type rawobjid =	string*string*int

 type objidtable =	(string * objid) list 

 datatype mibtree = 	MIBTREE of object option * 
				{branchname:string,
				number:int,
				branch:mibtree} list 
			
			
 exception NodeInPath
 exception BranchAlreadyExists 
 exception NodeIsAlreadyHere

 datatype mibvalue = 	INT of LargeInt.int | 
			OCTETSTRING of Word8Vector.vector |
			NULL | 
			SEQUENCE of mibvalue list | 
			SEQUENCEOF of mibvalue list | 
			OBJ_ID of int list | 
			NETWORK_ADDRESS of Word8.word list | 
			IP_ADDRESS of Word8.word list | 
			COUNTER of Word32.word|
			GAUGE of Word32.word |
			TIMETICKS of Word32.word |
			DISPLAYSTRING of string |
			PHYS_ADDRESS of Word8Vector.vector |
			IMPLICITSEQUENCE of int * mibvalue list
		
 datatype tag = 	UNIVERSAL of int | APPLICATION of int | 
			PRIVATE of int | CONTEXT_SPECIFIC of int

 datatype coding =	PRIMITIVE | CONSTRUCTED


 fun tagOf (ty:mibvalue) = 
     case ty of	INT _		=> (UNIVERSAL 2,PRIMITIVE)
	|	OCTETSTRING _	=> (UNIVERSAL 4,PRIMITIVE)
	|	NULL		=> (UNIVERSAL 5,PRIMITIVE)
	|	SEQUENCE _	=> (UNIVERSAL 16,CONSTRUCTED)
	|	SEQUENCEOF _	=> (UNIVERSAL 16,CONSTRUCTED)
	|	OBJ_ID _	=> (UNIVERSAL 6,PRIMITIVE)
	|	NETWORK_ADDRESS _ => (APPLICATION 0,PRIMITIVE)
	|	IP_ADDRESS _	=> (APPLICATION 0,PRIMITIVE)
	|	COUNTER _	=> (APPLICATION 1,PRIMITIVE)
	|	GAUGE _		=> (APPLICATION 2,PRIMITIVE)
	|	TIMETICKS _	=> (APPLICATION 3,PRIMITIVE)
	|	DISPLAYSTRING _	=> (UNIVERSAL 4,PRIMITIVE)
	|	PHYS_ADDRESS _ 	=> (UNIVERSAL 4,PRIMITIVE)
	|	IMPLICITSEQUENCE (number,_)
			=> (CONTEXT_SPECIFIC number,CONSTRUCTED) 

 fun toString (mibValue:mibvalue) = 
     case mibValue of 
       INT number 		=> LargeInt.toString number
     | OCTETSTRING w8v		=> 
	implode (map (chr o Word8.toInt) (Word8Vector.foldr (op ::) [] w8v) )
     | NULL			=> "NULL"
     | OBJ_ID (first::rest)	=> 
	(Int.toString first) ^ 
	(concat (map (fn n => ("." ^ (Int.toString n)) ) rest) )	  
     | NETWORK_ADDRESS [w1,w2,w3,w4] => 
			let val toS = (Int.toString o Word8.toInt)
			 in (toS w1) ^ "." ^ (toS w2) ^ "." ^
			    (toS w3) ^ "." ^ (toS w4)
			end
     | IP_ADDRESS [w1,w2,w3,w4] => 
                        let val toS = (Int.toString o Word8.toInt)   
                         in (toS w1) ^ "." ^ (toS w2) ^ "." ^
                            (toS w3) ^ "." ^ (toS w4)
                        end
     | COUNTER w32		=> Word32.fmt StringCvt.DEC w32
     | GAUGE w32		=> Word32.fmt StringCvt.DEC w32
     | TIMETICKS w32		=> Word32.fmt StringCvt.DEC w32
     | DISPLAYSTRING str	=> str
     | PHYS_ADDRESS w8v 	=>
		let val (first::rest) = Word8Vector.foldr (op ::) [] w8v
		 in concat ((Word8.toString first)::
			    (map (fn w => (":" ^ (Word8.toString w))) rest)   )
		end
	

 fun word8ListFromWord32 w = 
 let fun curriedAndb u v = Word32.andb(u,v)
     val word8FromWord32Lsb =
	 Word8.fromInt o Word32.toInt o (curriedAndb (0wxFF:Word32.word))
     fun sr bits w32 = Word32.>>(w32,Word.fromInt bits)
  in map word8FromWord32Lsb [sr 24 w,sr 16 w,sr 8 w,w]
 end

 fun identifierOctets (t:tag,c:coding) = 
 let 
   open Word8
   fun c2word8 PRIMITIVE = fromInt 0
     | c2word8 CONSTRUCTED = fromInt 32
     (* the type of coding is coded in the 6th bit 
        (bits are numbered from 1 to 8) 		*)
   fun curriedOrb u v = orb(u,v)
   val addCoding = curriedOrb (c2word8 c)
 in	
   Word8Vector.fromList 
   [
   case t of UNIVERSAL number	=> addCoding (fromInt number)
	|    APPLICATION number	=> addCoding (orb(fromInt 64,fromInt number))
	|    CONTEXT_SPECIFIC number	
				=> addCoding (orb(fromInt 128,fromInt number))
	|    PRIVATE number	=> addCoding (orb(fromInt 192,fromInt number))
   ]
 end

 fun lengthOctets (l:int) = 
   if let open Int in (l <= 127) end 
		then Word8Vector.fromList [Word8.fromInt l]
		else
     let open Word32
	 val w = fromInt l
	 fun curriedWord32andb u v = andb(u,v)
	 val intFromWord32Lsb = 
		toInt o (curriedWord32andb (fromInt 255)) 
	 	(* Make an integer from the less significant byte of 
		   a 32 bit word *)
	 fun sr bits w32 = >>(w32,Word.fromInt bits)
		(* Shift right by 'bits' bits *)
	 fun dropZeros (0::xs) = dropZeros xs
	   | dropZeros xs = xs

	 val bytelist = 
		map Word8.fromInt 
		(dropZeros 
		(map intFromWord32Lsb [sr 24 w,sr 16 w,sr 8 w,w]) )
	     (* creates a list containing the bytes of the 32 bit word,
		the most significant byte is the head of the list       *)

      in Word8Vector.fromList 
	(Word8.orb(Word8.fromInt 128,Word8.fromInt(length(bytelist)))::bytelist)
     end


 fun encodeSubIdentifier (subId:int) = 
 let open Word32
     val w = fromInt subId
     fun curriedWord32andb u v = andb(u,v)
     val word8FromWord32Ls7Bit = 
	 Word8.fromInt o toInt o (curriedWord32andb(fromInt 127))
     fun sr bits w32 = >>(w32,Word.fromInt bits)
                (* Shift right by 'bits' bits *)
     fun dropZeros (((0wx0):Word8.word)::xs) = dropZeros xs
       | dropZeros zs = zs
     fun set8thBits (lastbyte as w::[]) = lastbyte
       | set8thBits (w::ws) = Word8.orb(0wx80,w)::set8thBits ws
     val bytelist = set8thBits (dropZeros (map word8FromWord32Ls7Bit 
					  [sr 21 w,sr 14 w,sr 7 w,w])  )
  in Word8Vector.fromList bytelist 
 end

 fun encSubId subId =
 let val srByMof7Bits = fn index =>
	 (Word8.fromLargeWord o 
	  Word32.toLargeWord)  
          (Word32.andb(0wx7f,Word32.>>(subId,Word.fromInt(index) * 0wx7)))
     fun dropZeros [0wx00] = [0wx00]
       | dropZeros (((0wx0):Word8.word)::xs) = dropZeros xs
       | dropZeros xs = xs
     fun set8thBits (lastbyte as w::[]) = lastbyte
       | set8thBits (w::ws) = Word8.orb(0wx80,w)::set8thBits ws
     val bytelist = set8thBits(dropZeros(rev(List.tabulate(4,srByMof7Bits))))
  in Word8Vector.fromList bytelist
 end 

 local 
  open Word8Vector
 in   
 fun contentsOctetsOf mibValue =
     case mibValue of 
     (INT number) 		=> let val (LongInt.LONGINT ws) = 
					LongInt.fromLargeInt number
	 			    in fromList ws end
   | (OCTETSTRING octetvector)	=> octetvector
   | NULL 			=> fromList []
   | (SEQUENCE mibValues)	=> concat(map encode mibValues)
   | (SEQUENCEOF mibValues) 	=> concat(map encode mibValues)
   | (OBJ_ID (first::second::rest)) =>
      concat (map (encSubId o Word32.fromInt) ((first*40+second)::rest) )
   | (NETWORK_ADDRESS w8s)	=> fromList w8s
   | (IP_ADDRESS w8s)		=> fromList w8s
   | (COUNTER w32) 		=> let val (LongInt.LONGINT ws) = 
						LongInt.fromWord32 w32
				    in fromList ws end
   | (GAUGE w32)		=> let val (LongInt.LONGINT ws) =
                                                LongInt.fromWord32 w32
                                    in fromList ws end
   | (TIMETICKS w32)		=> let val (LongInt.LONGINT ws) =
                                                LongInt.fromWord32 w32
                                    in fromList ws end
   | (DISPLAYSTRING strng)	=> 
		fromList(map (Word8.fromInt o ord) (explode strng))
   | (PHYS_ADDRESS octetvector)	=> octetvector
   | (IMPLICITSEQUENCE (_,mibValues)) => concat (map encode mibValues)

 and encode (mibValue:mibvalue) =
     let val contentsOctets' = contentsOctetsOf (mibValue)
      in concat [identifierOctets(tagOf mibValue),
 		 lengthOctets(length contentsOctets'),
		 contentsOctets' ]
     end

 fun tagAndCodingOf w8 =
 let val number = Word8.toInt ( Word8.andb (0wx1F,w8) )
     val c = case Word8.andb(0wx20,w8) of 0wx00 => PRIMITIVE
					| 0wx20 => CONSTRUCTED
     val tagof = case Word8.andb(0wxC0,w8) of 0wx00 => UNIVERSAL number
					    | 0wx40 => APPLICATION number
					    | 0wx80 => CONTEXT_SPECIFIC number
					    | 0wxC0 => PRIVATE number
  in (tagof,c)
 end

 fun identifierAndLengthOf (encoding:Word8Vector.vector) =
 let val identifierOctet = sub(encoding,0)
     val firstLengthOctet = sub(encoding,1)
     val intOfLs7Bit = Word8.toInt (Word8.andb(0wx7F,firstLengthOctet))
     val shortForm = Word8.andb(0wx80,firstLengthOctet) = 0wx00
     val contentsLength = if shortForm
	then intOfLs7Bit
	else if intOfLs7Bit = 0 
		then raise NotImplemented "indefinit length octets"
		else
    (Word32.toInt o LongInt.toWord32 o LongInt.minimize)
    (LongInt.LONGINT 
	(0wx00::
	   (foldr (op ::) [] (extract(encoding,2,SOME intOfLs7Bit)) )
        )
    )
     val contentsStart = if shortForm then 2
				      else 2 + intOfLs7Bit
  in (identifierOctet,contentsStart,contentsLength) 
 end

 fun vectorToOctetString v =
 let fun vectorToOctetStringList vv =
     let val (id,from,sizeOf) = identifierAndLengthOf vv
	 val (t,c) = tagAndCodingOf id
      in case t of UNIVERSAL 4 => 
	    (case c of PRIMITIVE => 
		if length vv = from + sizeOf then [extract(vv,from,NONE)]
					   else extract(vv,from,SOME sizeOf)::
		vectorToOctetStringList(extract(vv,from+sizeOf,NONE))      
		     | CONSTRUCTED =>
		if length vv = from + sizeOf 
		then vectorToOctetStringList(extract(vv,from,NONE))
		else vectorToOctetStringList(extract(vv,from,SOME sizeOf)) @
			vectorToOctetStringList(extract(vv,from+sizeOf,NONE))
	    ) (* end case c *)
		 | _ => raise BadEncoding "Hey, this coding is illegal! (garbage in a constructed octetstring encoding)"
     end (* vectorToOctetStringList *)
     
  in concat (vectorToOctetStringList v)
 end (* vectorToOctetString *)

 fun decodeObjectIdentifier encoding = 
 let fun subIdLength enc n = if Word8.andb(sub(enc,n),0wx80)=0wx00 
				then (n+1)
			  	else subIdLength enc (n+1)
     fun encodedSubIdList enc =
     let val lengthOfFirst = subIdLength enc 0
      in if lengthOfFirst = length enc 
	    then [extract(enc,0,NONE)]
 	    else extract(enc,0,SOME lengthOfFirst)::
		 encodedSubIdList(extract(enc,lengthOfFirst,NONE))
     end
     val shiftLeftAndPut = fn (w8,w32) => 
	 Word32.orb(Word32.<<(w32,0wx07),
	    (Word32.fromLargeWord o Word8.toLargeWord) (Word8.andb(0wx7F,w8)) )
     fun expandFirst (x::xs) = (x div 40)::(x mod 40)::xs
	     (* the first encoding is X * 40 + Y, where X is the first,
		Y is the second subidentifier				*)
     
  in expandFirst(map 
		 (Word32.toInt o (foldl shiftLeftAndPut 0wx0)) 
		 (encodedSubIdList encoding)
		)
	     (* this foldl is Word8Vector.foldl! 			*)
 end 

 fun Word8VectorToWord32 vec=
 let val shiftLeft8andOr = 
     fn (w8,w32) => 
	Word32.orb(Word32.<<(w32,0wx08),
		(Word32.fromLargeWord o Word8.toLargeWord) w8)
  in foldl shiftLeft8andOr 0wx00 vec
 end

 fun decode encoding =
 let val (id,from,sizeOf) = identifierAndLengthOf encoding
     val foo = if (from + sizeOf) <> (length encoding) then 
			raise BadEncoding "Oh, it's not only one value!"
			else ()
     val (t,c) = tagAndCodingOf id
     val contentsOctets = extract(encoding,from,NONE)
  in case t of 
       UNIVERSAL 2 => (INT o Word32.toLargeInt o LongInt.toWord32)
	(LongInt.LONGINT(foldr (op ::) [] contentsOctets) )
		(* integers in SMI are representable in 32 bits 	*)
     | UNIVERSAL 4 => (OCTETSTRING o vectorToOctetString) encoding
		(* the vectorToOctetString function needs the identifer
		   and length octets					*)
     | UNIVERSAL 5 => NULL
     | UNIVERSAL 16 => SEQUENCE ( decodeToList contentsOctets )
     | UNIVERSAL 6 => OBJ_ID (decodeObjectIdentifier contentsOctets)
     | APPLICATION 0 => NETWORK_ADDRESS (foldr (op ::) [] contentsOctets)
     | APPLICATION 1 => COUNTER (Word8VectorToWord32 contentsOctets)
     | APPLICATION 2 => GAUGE (Word8VectorToWord32 contentsOctets)
     | APPLICATION 3 => TIMETICKS (Word8VectorToWord32 contentsOctets)
     | CONTEXT_SPECIFIC number => 
		IMPLICITSEQUENCE(number,decodeToList contentsOctets)
 
 end (* decode *)

 and decodeToList enc =
 let val (id,from,sizeOf) = identifierAndLengthOf enc
     val lengthOfFirstValue = from + sizeOf 
  in if lengthOfFirstValue = length enc 
	then [decode enc]
	else decode(extract(enc,0,SOME lengthOfFirstValue))::
			decodeToList(extract(enc,lengthOfFirstValue,NONE))
 end (* decodeToList *)  


 end (* local open Word8Vector *)

	

 fun putObject (idList:objid,obj:object,
		(mibTree as MIBTREE (objectOption,subTrees)) ) = 
 let val id = hd idList
     val isId = fn (x:{branchname:string,
			number:int,
			branch:mibtree}) => (#number x = id)
     val (brs,others) = List.partition isId subTrees
  in case brs of 
       [] => if length idList = 1 
   		then MIBTREE (objectOption,
				{branchname = #name obj,
				 number = id,
				 branch = MIBTREE (SOME obj,[])} :: others)
		else MIBTREE (objectOption,
				{branchname = "",
				 number = id,
				 branch = putObject(tl idList,obj,
						MIBTREE (NONE,[]))} :: others)   
				(* makes the whole path to the object's place *)
     | _  => let val br = hd brs
		 val (MIBTREE (NONE,brSubTrees)) = #branch br
	     in if length idList = 1 
		then 
		(if (#branchname br) = "" 
			then MIBTREE(objectOption, 
		{branchname = #name obj,
		 number = #number br,
		 branch = MIBTREE (SOME obj,brSubTrees) }	::others) 
			else 
	raise Err ("Branch already exists (putObject) " ^ (#name obj) ^ 
	"already here:" ^ (#branchname(hd brs)) ^  
	(concat	(map (fn num => (Int.toString num) ^ ",\n") idList) ) 
		  )
		)else MIBTREE (objectOption,
				{branchname = #branchname br,
				 number = id,
				 branch = 
	(putObject(tl idList,obj,#branch br) handle (Err ss) => 
			raise Err ((Int.toString id) ^ "," ^ ss))}
				::
				 others)
 	     end
		     
 end (* putObject *)

 fun putSubtree (idList:objid,subTreeName,
			(mibTree as MIBTREE(objectOption,subTrees)) ) = 
 let val id = hd idList
     val isId = fn (x:{branchname:string,
                       number:int,
                       branch:mibtree}) => (#number x = id)
     val (brs,others) = List.partition isId subTrees
  in case brs of
       [] => if length idList = 1
		then MIBTREE (objectOption,
				{branchname = subTreeName,
				 number = id,
		 		 branch = MIBTREE (NONE,[])} ::others)
		else MIBTREE (objectOption,
				{branchname = "",
				 number = id,
				 branch = putSubtree 
				(tl idList,subTreeName, MIBTREE (NONE,[]) )
	  			 } :: others )
      | _ => if length idList = 1
		then raise Err "Branch already exists (putSubtree)"
		else let val br = hd brs
		      in MIBTREE (objectOption,
				{branchname = #branchname br,
				 number = id,
				 branch = 
				  putSubtree(tl idList,subTreeName,#branch br)}
				::
				 others)
		     end
 end (* putSubtree *)

 
 
 fun lookUpObjId name [] = raise Err ("ObjId: " ^ name)
   | lookUpObjId name (n::ns) = if name = #1 n then SOME (#2 (n:string*objid))
					       else lookUpObjId name ns

 fun lookUpType name [] = raise Err ("Type: " ^ name)
   | lookUpType name (n::ns) = 
	if name = # 1 n then SOME (#2 (n:string*mibtype))
			else lookUpType name ns

  val root = [("iso",[1])]:objidtable
  val (rawObjIdTable:rawobjid list) =  [("org","iso",3),
			("dod","org",6),
			("internet","dod",1),
			("mgmt","internet",2)]
 
 fun digestRawObjId (rawObjId:rawobjid,
		     (objIdTable:objidtable,mibTree:mibtree)) =
 let val objId = valOf (lookUpObjId (#2 rawObjId) objIdTable) @ [#3 rawObjId]
  in ( (#1 rawObjId,objId)::objIdTable, putSubtree(objId,#1 rawObjId,mibTree) )
 end 

 fun putObjIdToTable (rawObjId:rawobjid,objIdTable:objidtable) = 
 let val objId = valOf (lookUpObjId (#2 rawObjId) objIdTable) @ [#3 rawObjId]
  in (#1 rawObjId,objId)::objIdTable
 end 

(*
 fun digestRawObjIdList([],objIdTable,mibTree) = (objIdTable,mibTree)
   | digestRawObjIdList(rawObjIdList as head::tail,objIdTable,mibTree) = 
     let val (newObjIdTable,newMibTree) = 
		digestOneRawObjId (head,objIdTable,mibTree)
      in digestRawObjIdList(tail,newObjIdTable,newMibTree)
     end
*)
 fun makeRawObjIdList [] :rawobjid list = []
   | makeRawObjIdList (asmnt::asnmntList) = 
     case asmnt of 
       VALUE rawOIRow => rawOIRow :: makeRawObjIdList asnmntList
     | OBJECT rawObject => 
       (#name rawObject, 
	#1(#objid rawObject) , 
	#2(#objid rawObject)) :: makeRawObjIdList asnmntList
     | _ => makeRawObjIdList asnmntList


(* This function builds the symbol table, using the fact that the only
   type assignments in RFC1213 are solely of type SEQUENCE		*)

 fun buildSymbolTable [] = []:symboltable
   | buildSymbolTable (asgn::asgnList) =
     case asgn of TYPE (symbolTableRow as (reference,mibType)) => 
			(case mibType of SEQUENCE_T _ => 
				symbolTableRow::buildSymbolTable(asgnList)
			| _ => buildSymbolTable(asgnList)
			)
     | _ => buildSymbolTable(asgnList)

fun mibTypeToString mibType =
 	 case mibType of REF strng => strng
	 | SEQUENCEOF_T mType => "SEQUENCE OF " ^ mibTypeToString mType
	 | SEQUENCE_T nameAndBTypeList => "SEQUENCE " ^ 
	String.concat 
       (map(fn x => (#1 x ^ ":" ^ basicTypeToString (#2 x) ^ " ")) nameAndBTypeList)
	 | BASIC bType => basicTypeToString bType

and basicTypeToString basicType =
	  (case basicType of NULL_T	=> "NULL"
		| OBJ_ID_T 		=> "OBJECT IDENTIFIER"
		| NETWORK_ADDRESS_T 	=> "NetworkAddress"
		| IP_ADDRESS_T 		=> "IpAddress"
		| COUNTER_T 		=> "Counter"
		| GAUGE_T 		=> "Gauge"
		| TIMETICKS_T 		=> "TimeTicks"
		| DISPLAYSTRING_T siz	=> "DISPLAYSTRING" ^
					(case siz of NONE => ""
					| SOME (n1,n2) =>
					" (SIZE (" ^ (Int.toString n1) ^
					".." ^ (Int.toString n2) ^ "))" )
		| PHYS_ADDRESS_T	=> "PhysAddress"
		| OCTETSTRING_T		=> "OCTET STRING"
		| INT_T intType		=> "INTEGER" ^
		 (case intType of SIMPLE => ""
		  | SUBTYPE_SPEC (n1,n2) => 
		    " (" ^ (Int.toString n1) ^ ".." ^ (Int.toString n2) ^ ")"
		  | NAME_AND_NUMBER_LIST strIntList =>
		  let val first = hd strIntList
		      val rest = tl strIntList
			
	in String.concat ([" {",#1 first,"(",Int.toString (#2 first),")"]
	 @ (map (fn x => "," ^ (#1 x) ^ "(" ^ Int.toString (#2 x) ^ ")" ) rest)
	 @ ["}"])
		  end (* let *)
 		 ) (* end case intType *)
	  ) (* end case basicType *)


 fun digestOneRawObject(rawObject:rawobject,
			symbolTable:symboltable,
			objIdTable:objidtable,
			mibTree:mibtree) =
 let val mibTypeToStringAndMibType = 
	 fn mT => case mT of REF strng => (strng,valOf(lookUpType strng symbolTable) )
				| _  => ("NoName",mT)
     val obj =  
	{name = #name rawObject,
 	 syntaxname = mibTypeToString ( #syntax rawObject ),
	 syntax = 
	   (case #syntax rawObject of 
		  REF typeName => valOf(lookUpType typeName symbolTable)
		| other => other),
	 access = #access rawObject,
	 status = #status rawObject,
	 indextypes = map mibTypeToStringAndMibType (#index rawObject) ,
 	 descr = #descr rawObject}
     val newSymbolTable = (#name obj,#syntax obj)::symbolTable
     val newMibTree = 
	 putObject(valOf(lookUpObjId (#name rawObject) objIdTable),obj,mibTree)
  in (newSymbolTable,objIdTable,newMibTree)
 end (* digestOneRawObject *)

 fun buildMib ([],sT,oT,mT) = (sT,oT,mT)
   | buildMib (asgn::assignmentList,symbolTable:symboltable,
				    objIdTable:objidtable,
				    mibTree:mibtree) = 
     (case asgn of (OBJECT rawObject) =>
     let val (newSymT,newOIT,newMT) = 
	 digestOneRawObject(rawObject,symbolTable,objIdTable,mibTree)
      in 
	 buildMib(assignmentList,newSymT,newOIT,newMT)
     end
     | _ => buildMib(assignmentList,symbolTable,objIdTable,mibTree)     )

end (* Mib *)
