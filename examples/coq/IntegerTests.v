Require Import Basic.
Require Import Full.
Require Import Rosette.Quantified.
Require Import ListEx.
Require Import Integer.

Definition solveAddTransSpace : Space (Int * Int * Int * Int * Int) :=
  bind full (fun x:Int =>
  bind full (fun y:Int => 
  bind full (fun z:Int => 
    let a := plus (plus x y) z in
    let b := plus x (plus y z) in
      if equal a b then Basic.empty else single (x,y,z,a,b)))).

Definition solveAddTrans : Result (Int * Int * Int * Int * Int) :=
  search solveAddTransSpace.

Definition solveAddAddTrans : Result (Int * Int * Int * Int * Int) :=
  search (
    bind full (fun x:Int =>
    bind full (fun y:Int => 
    bind full (fun z:Int => 
      let a := plus (plus x (plus y y)) z in
      let b := plus x (plus y z) in
        if equal a b then empty else single (x,y,z,a,b))))).

Definition addTest :=
  let x := one in
  let y := one in
  let z := one in
  let a := plus (plus x (plus y y)) z in
  let b := plus x (plus y z) in
    equal a b.


Extraction Language Scheme.

Extraction "integer-tests" solveAddTransSpace solveAddTrans solveAddAddTrans addTest.
