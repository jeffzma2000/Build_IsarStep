(*
  Title: an implementation of Base64 encoding
  Author: Wenda Li (liwenda1990@hotmail.com / wl302@cam.ac.uk)
  
  This is aimed to implement RFC 3548, and be compatible with the Python 
    base64 (https://docs.python.org/3/library/base64.html). 
*)
signature BASE64 =
sig
  val codes : string;
  val pad : char;
  val encode : string -> string;
  val decode : string -> string;
end;

structure Base64 : BASE64 =
struct

val codes = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";

val pad = #"=";

exception DecodingError of string;

(* a character to ASCII index (within [0,255]) *)
fun chr_to_ascii c = Word8.fromInt (Char.ord c);

(* an ASCII index to the corresponding character *)
fun ascii_to_chr w = Char.chr (Word8.toInt w);

(* a code index (within [0,63]) to the corresponding code character *)
fun cindex_to_code w = String.sub (codes, Word8.toInt w);

(* a code character to the corresponding code index ([0,63]) *)
fun code_to_cindex c= 
  let
    val i = Char.ord c
  in
    if i >= 97 andalso i<=122 then 
      Word8.fromInt (i - 71)
    else if i >= 65 andalso i<=90 then
      Word8.fromInt (i - 65)
    else if i >= 48 andalso i<=57 then
      Word8.fromInt (i+4)
    else if i=47 then
      0w63
    else if i = 43 then
      0w62
    else 
      raise DecodingError ("Unrecognised code with ASCII index: "^ Int.toString i)
  end;

fun encode ss = 
    let
      val (q, r) = IntInf.quotRem(String.size ss, 3)
      val (len,q') = if r = 0 then (4*q,q) else (4*(q+1),q+1)
      val xs = CharVector.tabulate (len, 
          fn x => 
              let 
                val (xq, xr) = IntInf.quotRem(x, 4)
                val w0 = chr_to_ascii(String.sub(ss,xq*3))
                val w1 = chr_to_ascii(String.sub(ss,xq*3+1)) handle Subscript => 0wx0
                val w2 = chr_to_ascii(String.sub(ss,xq*3+2)) handle Subscript => 0wx0
              in
                if xr = 0 then
                    cindex_to_code(Word8.>>(w0,0w2))
                else if xr = 1 then
                    cindex_to_code(Word8.xorb(
                          Word8.<<(Word8.andb(w0,0wx3),0w4)
                          ,Word8.>>(Word8.andb(w1,0wxF0),0w4)
                        ))
                else if xr = 2 then
                  if q' - 1 > xq orelse r <> 1 then 
                    cindex_to_code(Word8.xorb(
                            Word8.<<(Word8.andb(w1,0wxF),0w2)
                            , Word8.>>(w2,0w6)
                          ))
                  else
                    pad
                else (*xr=3*)
                  if q' - 1 > xq orelse r = 0 then
                    cindex_to_code(Word8.andb(w2,0wx3F))
                  else 
                    pad
              end);
    in xs end;

fun count_pad ss = 
  let
    val len = String.size ss
    val i = ref (len-1)
  in
    while !i>=0 andalso String.sub(ss,!i) = pad do (i:= !i-1);
    len - 1 - !i
  end;

fun decode ss =
  let
    val ss_len = String.size ss
    val pad_len = count_pad ss
    val (q, r) = IntInf.quotRem(ss_len, 4)
    val _ = if r <> 0 then 
              raise DecodingError "Length of the input string should be multiple of 4."
            else ()
    val _ = if pad_len >2 then 
              raise DecodingError "Number of paddings should not exceed 2."
            else ()
    val xs = CharVector.tabulate (q*3-pad_len, 
          fn x => 
              let 
                val (xq, xr) = IntInf.quotRem(x, 3)
                val w0 = code_to_cindex(String.sub(ss,xq*4))
                val w1 = code_to_cindex(String.sub(ss,xq*4+1)) 
                val w2 = code_to_cindex(String.sub(ss,xq*4+2)) handle DecodingError _ => 0wx0
                val w3 = code_to_cindex(String.sub(ss,xq*4+3)) handle DecodingError _ => 0wx0
              in
                if xr = 0 then
                   ascii_to_chr(Word8.xorb(
                          Word8.<<(w0,0w2)
                          ,Word8.>>(w1,0w4)
                        ))
                else if xr = 1 then
                   ascii_to_chr(Word8.xorb(
                          Word8.<<(Word8.andb(w1,0wxF),0w4)
                          ,Word8.>>(w2,0w2)
                        ))
                else (* xr = 2 *)
                    ascii_to_chr(Word8.xorb(
                          Word8.<<(Word8.andb(w2,0wx3),0w6)
                          ,w3
                        ))
              end);
  in xs end;

end;