(* Copyright (C) 2019-2020 Matthew Fluet.
 * Copyright (C) 1999-2008 Henry Cejtin, Matthew Fluet, Suresh
 *    Jagannathan, and Stephen Weeks.
 * Copyright (C) 1997-2000 NEC Research Institute.
 *
 * MLton is released under a HPND-style license.
 * See the file MLton-LICENSE for details.
 *)

functor ImplementExceptions (S: XML_TRANSFORM_STRUCTS): XML_TRANSFORM =
struct

open S
datatype z = datatype Dec.t
datatype z = datatype PrimExp.t
structure Dexp = DirectExp

fun transform (Program.T {datatypes, body, ...}): Program.t =
   let
      (* topLevelHandler holds the ref cell containing the function of
       * type exn -> unit that should be called on unhandled exceptions.
       *)
      val topLevelHandlerType = Type.arrow (Type.exn, Type.unit)
      val topLevelHandlerVar = Var.newNoname ()
      val extraType =
         Exn.withEscape
         (fn escape =>
          let
             val _ =
                Exp.foreachPrimExp
                (body, fn (_, _, e) =>
                 case e of
                    PrimApp {prim, targs, ...} =>
                       (case prim of
                           Prim.Exn_extra =>
                              escape (Vector.first targs)
                         | Prim.Exn_setExtendExtra =>
                              escape (Vector.first targs)
                         | _ => ())
                  | _ => ())
          in
             Type.unit
          end)
      val dfltExtraVar = Var.newNoname ()
      val dfltExtraExp =
         if Type.isUnit extraType
            then Dexp.unit ()
         else let
                 val extraTycon = Type.tycon extraType
                 val extraCon =
                    Exn.withEscape
                    (fn escape =>
                     let
                        val _ =
                           Vector.foreach
                           (datatypes, fn {cons, tycon, ...} =>
                            if Tycon.equals (tycon, extraTycon)
                               then Vector.foreach
                                  (cons, fn {arg, con, ...} =>
                                   case arg of
                                      NONE => escape con
                                    | _ => ())
                            else ())
                     in
                        Error.bug "ImplementExceptions: can't find extraCon"
                     end)
              in
                 Dexp.conApp {arg = NONE,
                              con = extraCon,
                              targs = Vector.new0 (),
                              ty = extraType}
              end
      val extendExtraType = Type.arrow (extraType, extraType)
      val extendExtraVar = Var.newNoname ()
      val exnNameVar = Var.newString "exnName"
      (* sumType is the type of the datatype with all of the exn constructors. *)
      val {extraDatatypes,
           injectSum,
           projectExtra,
           projectSum,
           raisee,
           sumTycon,
           sumType
           } =
         if not (!Control.exnHistory)
            then {extraDatatypes = Vector.new0 (),
                  injectSum = fn e => e,
                  projectExtra = fn _ => Dexp.monoVar (dfltExtraVar, extraType),
                  projectSum = fn x => Dexp.monoVar (x, Type.exn),
                  raisee = (fn {exn, extend, ty, var} =>
                            [MonoVal {var = var, ty = ty,
                                      exp = Raise {exn = exn,
                                                   extend = extend}}]),
                  sumTycon = Tycon.exn,
                  sumType = Type.exn}
         else
            let
               val sumTycon = Tycon.newNoname ()
               val sumType = Type.con (sumTycon, Vector.new0 ())
               local
                  open Type
               in
                  val exnCon = Con.newNoname ()
                  val exnConArgType = tuple (Vector.new2 (extraType, sumType))
               end
               fun makeExn {exn, extra} =
                  let
                     open Dexp
                  in
                     conApp
                     {con = exnCon,
                      targs = Vector.new0 (),
                      ty = Type.exn,
                      arg = SOME (tuple {exps = Vector.new2 (extra, exn),
                                         ty = exnConArgType})}
                  end
               fun injectSum (exn: Dexp.t): Dexp.t =
                  makeExn {exn = exn,
                           extra = Dexp.monoVar (dfltExtraVar, extraType)}
               fun extractExtra x =
                  Dexp.select {tuple = x, offset = 0, ty = extraType}
               fun extractSum x =
                  Dexp.select {tuple = x, offset = 1, ty = sumType}
               fun extract (exn: Var.t, ty, f: Dexp.t -> Dexp.t): Dexp.t =
                  let
                     open Dexp
                     val tuple = Var.newNoname ()
                  in
                     casee
                     {test = monoVar (exn, Type.exn),
                      default = NONE,
                      ty = ty,
                      cases =
                      Cases.Con (Vector.new1
                                 (Pat.T {con = exnCon,
                                         targs = Vector.new0 (),
                                         arg = SOME (tuple, exnConArgType)},
                                  f (monoVar (tuple, exnConArgType))))}
                  end
               fun projectExtra (x: Var.t) =
                  extract (x, extraType, extractExtra)
               fun projectSum (x: Var.t) =
                  extract (x, sumType, extractSum)
               fun raisee {exn: VarExp.t,
                           extend: bool,
                           ty: Type.t,
                           var = x : Var.t}: Dec.t list =
                  let
                     open Dexp
                     val exp =
                        if not extend
                           then raisee {exn = varExp (exn, Type.exn),
                                        extend = false, ty = ty}
                        else
                           extract
                           (VarExp.var exn, ty, fn tup =>
                            raisee
                            {exn = makeExn
                             {exn = extractSum tup,
                              extra =
                              app
                              {func = deref (monoVar
                                             (extendExtraVar,
                                              Type.reff extendExtraType)),
                               arg = extractExtra tup,
                               ty = extraType}},
                             extend = false,
                             ty = ty})
                  in
                     vall {exp = exp, var = x}
                  end
               val extraDatatypes =
                  Vector.new1 {tycon = Tycon.exn,
                               tyvars = Vector.new0 (),
                               cons = Vector.new1 {con = exnCon,
                                                   arg = SOME exnConArgType}}
            in
               {extraDatatypes = extraDatatypes,
                injectSum = injectSum,
                projectExtra = projectExtra,
                projectSum = projectSum,
                raisee = raisee,
                sumTycon = sumTycon,
                sumType = sumType}
            end
      val {get = exconInfo: Con.t -> {nonceVar: Var.t,
                                      nonceTy: Type.t,
                                      make: VarExp.t option -> Dexp.t} option,
           set = setExconInfo, destroy} =
         Property.destGetSetOnce (Con.plist, Property.initConst NONE)
      val setExconInfo =
         Trace.trace2
         ("ImplementExceptions.setExconInfo",
          Con.layout, Layout.ignore, Unit.layout)
         setExconInfo
      val exconInfo =
         Trace.trace
         ("ImplementExceptions.exconInfo",
          Con.layout, Layout.ignore)
         exconInfo
      fun isExcon c =
         case exconInfo c of
            NONE => false
          | SOME _ => true
      val exnValCons: {con: Con.t, arg: Type.t} list ref = ref []
      val traceLoopDec =
         Trace.trace
         ("ImplementExceptions.loopDec", Dec.layout, List.layout Dec.layout)
      fun loop (e: Exp.t): Exp.t =
         let
            val {decs, result} = Exp.dest e
            val decs = List.concatRev (List.fold (decs, [], fn (d, ds) =>
                                                  loopDec d :: ds))
         in
            Exp.make {decs = decs,
                      result = result}
         end
      and loopDec arg: Dec.t list =
         traceLoopDec
         (fn (dec: Dec.t) =>
         case dec of
            MonoVal b => loopMonoVal b
          | Fun {decs, ...} =>
               [Fun {tyvars = Vector.new0 (),
                     decs = Vector.map (decs, fn {var, ty, lambda} =>
                                        {var = var,
                                         ty = ty,
                                         lambda = loopLambda lambda})}]
          | Exception {con, arg, elab} =>
               let
                  open Dexp
                  val nonceVar = Var.newString "exnNonce"
                  val (nonceTy, nonceDec) =
                     case elab of
                        ExnDecElab.App =>
                           (Type.unit,
                            vall {var = nonceVar, exp = unit ()})
                      | ExnDecElab.Gen =>
                           (Type.unitRef,
                            vall {var = nonceVar, exp = reff (unit ())})
                  val nonce = monoVar (nonceVar, nonceTy)
                  fun conApp arg =
                     injectSum (Dexp.conApp {con = con,
                                             targs = Vector.new0 (),
                                             ty = sumType,
                                             arg = SOME arg})
                  val (arg, make) =
                     case arg of
                        NONE =>
                           (* If the exception is not value carrying,
                            * then go ahead and make it now.
                            *)
                           let
                              val exn = Var.newString (Con.originalName con)
                           in
                              (nonceTy,
                               fn NONE => conApp nonce
                                | _ => Error.bug "ImplementExceptions: nullary excon applied to arg")
                           end
                      | SOME t =>
                           let
                              val tupleType = Type.tuple (Vector.new2 (nonceTy, t))
                           in
                              (tupleType,
                               fn SOME x => (conApp o tuple)
                                            {exps = Vector.new2 (nonce, varExp (x, t)),
                                             ty = tupleType}
                                | _ => Error.bug "ImplmentExceptions: unary excon not applied to arg")
                           end
               in
                  setExconInfo (con, SOME {nonceVar = nonceVar, nonceTy = nonceTy, make = make})
                  ; List.push (exnValCons, {con = con, arg = arg})
                  ; nonceDec
               end
          | _ => Error.bug "ImplementExceptions: saw unexpected dec") arg
      and loopMonoVal {var, ty, exp} : Dec.t list =
         let
            fun primExp e = [MonoVal {var = var, ty = ty, exp = e}]
            fun keep () = primExp exp
            fun makeExp e = Dexp.vall {var = var, exp = e}
         in
            case exp of
               Case {test, cases, default} =>
                  let
                     fun normal () =
                        primExp (Case {cases = Cases.map (cases, loop),
                                       default = Option.map (default, loop),
                                       test = test})
                  in
                     case cases of
                        Cases.Con cases =>
                           if Vector.isEmpty cases
                              then normal ()
                           else
                              let
                                 val (Pat.T {con, ...}, _) =
                                    Vector.first cases
                              in
                                 if not (isExcon con)
                                    then normal ()
                                 else (* convert to an exception match *)
                                    let
                                       open Dexp
                                       val defaultVar = Var.newString "default"
                                       fun callDefault () =
                                          app {func = (monoVar
                                                       (defaultVar,
                                                        Type.arrow
                                                        (Type.unit, ty))),
                                               arg = unit (),
                                               ty = ty}
                                       val unit = Var.newString "unit"
                                       val body =
                                          case default of
                                             NONE =>
                                                Error.bug "ImplementExceptions: no default for exception case"
                                           | SOME e =>
                                                fromExp (loop e, ty)
                                       val decs =
                                          vall
                                          {var = defaultVar,
                                           exp = lambda {arg = unit,
                                                         argType = Type.unit,
                                                         body = body,
                                                         bodyType = ty,
                                                         mayInline = true}}
                                    in
                                       makeExp
                                       (lett
                                        {decs = decs,
                                         body =
                                         casee
                                         {test = projectSum (VarExp.var test),
                                          ty = ty,
                                          default = SOME (callDefault ()),
                                          cases =
                                          Cases.Con
                                          (Vector.map
                                           (cases, fn (Pat.T {con, arg, ...}, e) =>
                                            let
                                               val {nonceVar, nonceTy, ...} = 
                                                  valOf (exconInfo con)
                                               val testVar = Var.newNoname ()
                                               val body =
                                                  iff {test =
                                                       equal
                                                       (monoVar
                                                        (testVar, nonceTy),
                                                        monoVar
                                                        (nonceVar, nonceTy)),
                                                       ty = ty,
                                                       thenn = (fromExp
                                                                (loop e, ty)),
                                                       elsee = callDefault ()}
                                               fun make (arg, body) =
                                                  (Pat.T
                                                   {con = con,
                                                    targs = Vector.new0 (),
                                                    arg = SOME arg},
                                                   body)
                                            in
                                               case arg of
                                                  NONE =>
                                                     make ((testVar, nonceTy), body)
                                                | SOME (x, t) =>
                                                     let
                                                        val tuple =
                                                           (Var.newNoname (),
                                                            Type.tuple (Vector.new2
                                                                        (nonceTy, t)))
                                                     in
                                                        make (tuple,
                                                              detupleBind
                                                              {tuple = monoVar tuple,
                                                               components =
                                                               Vector.new2 (testVar, x),
                                                               body = body})
                                                     end
                                            end))}})
                                    end
                              end
                      | _ => normal ()
                  end
             | ConApp {con, arg, ...} =>
                  (case exconInfo con of
                      NONE => keep ()
                    | SOME {make, ...} => makeExp (make arg))
             | Handle {try, catch = (catch, ty), handler} =>
                  primExp (Handle {try = loop try,
                                   catch = (catch, ty),
                                   handler = loop handler})
             | Lambda l => primExp (Lambda (loopLambda l))
             | PrimApp {args, prim, ...} =>
                  let
                     fun deref (var, ty) =
                        primExp
                        (PrimApp {prim = Prim.Ref_deref {readBarrier = true},
                                  targs = Vector.new1 ty,
                                  args = Vector.new1 (VarExp.mono var)})
                     fun assign (var, ty) =
                        primExp
                        (PrimApp {prim = Prim.Ref_assign {writeBarrier = true},
                                  targs = Vector.new1 ty,
                                  args = Vector.new2 (VarExp.mono var,
                                                      Vector.first args)})
                  in
                     case prim of
                        Prim.Exn_extra =>
                           (makeExp o projectExtra)
                           (VarExp.var (Vector.first args))
                      | Prim.Exn_name =>
                           (primExp o App)
                           {func = VarExp.mono exnNameVar,
                            arg = Vector.first args}
                      | Prim.Exn_setExtendExtra =>
                           assign (extendExtraVar,
                                   extendExtraType)
                      | Prim.TopLevel_getHandler =>
                           deref (topLevelHandlerVar,
                                  topLevelHandlerType)
                      | Prim.TopLevel_setHandler =>
                           assign (topLevelHandlerVar,
                                   topLevelHandlerType)
                      | _ => primExp exp
                  end
             | Raise {exn, extend} =>
                  raisee {exn = exn, extend = extend, ty = ty, var = var}
             | _ => keep ()
         end
      and loopLambda l =
         let
            val {arg, argType, body, mayInline} = Lambda.dest l
         in
            Lambda.make {arg = arg,
                         argType = argType,
                         body = loop body,
                         mayInline = mayInline}
         end
      val body = Dexp.fromExp (loop body, Type.unit)
      val exnValCons = Vector.fromList (!exnValCons)
      val datatypes =
         Vector.concat
         [Vector.new1
          {tycon = sumTycon,
           tyvars = Vector.new0 (),
           cons = Vector.map (exnValCons, fn {con, arg} =>
                              {con = con, arg = SOME arg})},
          extraDatatypes,
          datatypes]
      val body =
         Dexp.let1
         {body = body,
          exp = let
                   val exn = Var.newNoname ()
                in
                   Dexp.lambda
                   {arg = exn,
                    argType = Type.exn,
                    body = (Dexp.casee
                            {test = projectSum exn,
                             cases =
                             Cases.Con
                             (Vector.map
                              (exnValCons, fn {con, arg} =>
                               (Pat.T {con = con,
                                       targs = Vector.new0 (),
                                       arg = SOME (Var.newNoname (), arg)},
                                Dexp.const (Const.string (Con.originalName con))))),
                             default = NONE,
                             ty = Type.string}),
                    bodyType = Type.string,
                    mayInline = true}
                end,
             var = exnNameVar}
      val body =
         Dexp.let1
         {body = body,
          exp = (Dexp.reff
                 (Dexp.lambda
                  {arg = Var.newNoname (),
                   argType = extraType,
                   body = (Dexp.sequence o Vector.new2)
                          (Dexp.bug "extendExtra unimplemented",
                           Dexp.monoVar (dfltExtraVar, extraType)),
                   bodyType = extraType,
                   mayInline = true})),
          var = extendExtraVar}
      val body =
         Dexp.let1
         {body = body,
          exp = dfltExtraExp,
          var = dfltExtraVar}
      val body =
         let
            val x = (Var.newNoname (), Type.exn)
         in
            Dexp.handlee
            {try = body,
             ty = Type.unit,
             catch = x,
             handler = Dexp.app {func = (Dexp.deref
                                         (Dexp.monoVar
                                          (topLevelHandlerVar,
                                           Type.reff topLevelHandlerType))),
                                 arg = Dexp.monoVar x,
                                 ty = Type.unit}}
         end
      val body =
         Dexp.let1
         {var = topLevelHandlerVar,
          exp = Dexp.reff (Dexp.lambda
                           {arg = Var.newNoname (),
                            argType = Type.exn,
                            body = Dexp.bug "toplevel handler not installed",
                            bodyType = Type.unit,
                            mayInline = true}),
          body = body}
      val body =
         Dexp.handlee
         {try = body,
          ty = Type.unit,
          catch = (Var.newNoname (), Type.exn),
          handler = Dexp.bug "toplevel handler not installed"}
      val body = Dexp.toExp body
      val program =
         Program.T {datatypes = datatypes,
                    body = body}
      val _ = destroy ()
   in
      program
   end

end
