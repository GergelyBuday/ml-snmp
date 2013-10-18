structure Snmp =
struct 

 exception WrongSnmpFormat

 fun makeSnmpMessage (community:string,data:Mib.mibvalue) =
     Mib.SEQUENCE 
     [Mib.INT 0, 	(* version is always 0 *)
     Mib.OCTETSTRING 
	(Word8Vector.fromList (map (Word8.fromInt o ord) (explode community))),
     data]

 val getRequest = 0
 val getNextRequest = 1
 val getResponse = 2
 val setRequest = 3

 fun makeSnmpPDU (pduType:int,
		  requestid:LargeInt.int,
                  errorstatus:LargeInt.int,
	  	  errorindex:LargeInt.int,
	          varBindList:(Mib.objid * Mib.mibvalue) list ) =
   Mib.IMPLICITSEQUENCE (pduType,  
   [Mib.INT requestid,
    Mib.INT errorstatus,
    Mib.INT errorindex,
    Mib.SEQUENCEOF(
	map 
	(fn (oId,oValue) => Mib.SEQUENCEOF [Mib.OBJ_ID oId,oValue]) 
	varBindList  )
   ] ) (* IMPLICITSEQUENCE *)
 
 fun getRequestPDU (requestid:LargeInt.int,oIdList:Mib.objid list) =
     makeSnmpPDU 
	(getRequest,requestid,0,0,map (fn oId => (oId,Mib.NULL)) oIdList)

 fun getNextRequestPDU (requestid:LargeInt.int,oIdList:Mib.objid list) =
     makeSnmpPDU
	(getNextRequest,requestid,0,0,map (fn oId => (oId,Mib.NULL)) oIdList)

 fun setRequestPDU (requestid:LargeInt.int,
		    varBindList:(Mib.objid*Mib.mibvalue) list) =
     makeSnmpPDU(setRequest,requestid,0,0,varBindList)
     
 fun fromSnmpPDU (pdu:Mib.mibvalue) = 
 let val (all as (ver,cV,rqId,err,errIdx,vBL)) = case pdu of 
      Mib.SEQUENCE [Mib.INT version,
		    Mib.OCTETSTRING communityVector,
		    Mib.IMPLICITSEQUENCE(2,[Mib.INT requestid,
					    Mib.INT errorstatus,
					    Mib.INT errorindex,
					    Mib.SEQUENCE (vBindingList)
					   ]  
					)	 
		   ] => 
	(version,communityVector,requestid,errorstatus,errorindex,vBindingList)
     | _ => raise WrongSnmpFormat
  in all (* (ver,cV,rqId,err,errIdx,vBL) *) 
 end (* fromSnmpPDU *)

end (* Snmp *)                         


