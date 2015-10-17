#require "batteries"
#require "qcheck"

#load "escher_types.cmo"
#load "escher_core.cmo"
#load "escher_components.cmo"
#load "escher_synth.cmo"
#load "specInfer.cmo"
(* #load "specify.cmo" *)
#load "testGen.cmo"

open Batteries
open Escher_types
open Escher_core
open Escher_components
open Escher_synth
open QCheck.Arbitrary
open SpecInfer
(* open Specify *)
open TestGen
