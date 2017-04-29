(*
 * grass.sml - Grass interpreter
 * http://www.blue.sky.or.jp/grass/
 *
 * Copyright (C) 2006, 2007 UENO Katsuhiro. All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in
 *    the documentation and/or other materials provided with the
 *    distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY THE AUTHOR AND CONTRIBUTORS ``AS IS''
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO,
 * THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR
 * PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE AUTHOR OR CONTRIBUTORS
 * BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
 * CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
 * SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR
 * BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY,
 * WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE
 * OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN
 * IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 * History:
 *
 * 2007-10-02
 *   - Follow the latest changes of the definition of Grass.
 * 2007-09-20
 *   - First version.
 *)

structure Grass : sig

  val RELEASE_DATE : string

  type value
  val run : string -> value
  val go : string -> value

end =
struct

  val RELEASE_DATE = "2007-10-02"

  datatype value = CH of int | PRIM of value -> value | FN of code * env
       and insn = App of int * int | Abs of int * code
  withtype code = insn list
       and env = value list

  (* evaluator *)

  fun input otherwise =
      case TextIO.input1 TextIO.stdIn of
        SOME x => CH (ord x)
      | NONE => otherwise

  fun output (CH c) =
      (TextIO.output1 (TextIO.stdOut, chr c);
       TextIO.flushOut TextIO.stdOut;
       CH c)
    | output x = raise Fail "out: not a char"

  fun succ (CH c) = CH ((c + 1) mod 256)
    | succ x = raise Fail "succ: not a char"

  val churchTrue  = FN([Abs(1, [App(3,2)])], [FN(nil, nil)])
  val churchFalse = FN([Abs(1, nil)], nil)

  fun charEq (CH c1, CH c2) = if c1 = c2 then churchTrue else churchFalse
    | charEq _ = churchFalse

  val initEnv = [PRIM output, PRIM succ, CH (ord #"w"), PRIM input]

  fun eval machine =
      case machine of
        (App(m, n)::c, e, d) =>
        let
          val (f, v) = (List.nth (e, m - 1), List.nth (e, n - 1))
                       handle Subscript => raise Fail "out of bound"
        in
          case f of
            CH _ => eval (c, charEq (f, v)::e, d)
          | PRIM f => eval (c, f v::e, d)
          | FN (c', e') => eval (c', v::e', (c, e)::d)
        end
      | (Abs(1, c')::c, e, d) => eval (c, FN (c', e)::e, d)
      | (Abs(n, c')::c, e, d) => eval (c, FN ([Abs(n - 1, c')], e)::e, d)
      | (nil, v::e, (c', e')::d) => eval (c', v::e', d)
      | (nil, v::nil, nil) => v
      | (nil, _, _) => raise Fail "BUG: illegal state"

  fun start code =
      eval (code, initEnv, [([App(1,1)], nil), (nil, nil)])

  (* parser *)

  fun count c n (h::t) = if c = h then count c (n+1) t else n :: count h 1 t
    | count (c:char) n nil = [n]

  fun app (x::y::z) = App (x, y) :: app z
    | app (h::t) = raise Fail "parse error at tail"
    | app nil = nil

  fun toplevel l =
      case count #"w" 0 l of
        nil => raise Fail "BUG"
      | 0::l => app l
      | h::t => [Abs (h, app t)]

  fun preprocess ss =
      List.filter (fn c => c = #"w" orelse c = #"W") (Substring.explode ss)

  fun parse src =
      let
        val ss = Substring.full src
        val ss = Substring.dropl (fn c => c <> #"w") ss
        val funcs = Substring.fields (fn c => c = #"v") ss
        val funcs = map preprocess funcs
        val funcs = List.filter (fn nil => false | _ => true) funcs
      in
        List.concat (map toplevel funcs)
      end

  (* toplevel *)

  fun run src =
      start (parse src)

  fun go filename =
      let
	val f = TextIO.openIn filename
	val s = TextIO.inputAll f handle e => (TextIO.closeIn f; raise e)
	val _ = TextIO.closeIn f
      in
        run s
      end

end
