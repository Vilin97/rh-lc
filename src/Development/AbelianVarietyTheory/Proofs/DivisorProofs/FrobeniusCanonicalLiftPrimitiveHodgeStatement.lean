module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusCanonicalLiftPrimitiveHodge
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsCharZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigOfOmegaInjectiveOfEqZero
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_primitiveSubmodule_of_isCan_of_rigToExt_eq_zero : ∀ (p : ℕ) [Fact p.Prime]  (R : Type) [CommRing R] (N : ℕ), (p : R) ^ N = 0 → ∀ (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ (G : PDivGroup p R) (t : G.TorsionTower A) (c : primDR A) (x : ((G.cocycles × G.omega) ⧸ _root_.LinearMap.range (G.cob.prod (_root_.LinearMap.codRestrict G.omegaSub ((_root_.LinearMap.piMap fun i => _root_.GlobalTheory.AugCot.d (_root_.Bialgebra.counitAlgHom _ (G.A i))).domRestrict G.funs) (fun b n => (_root_.GlobalTheory.PDiv.cotMap_d _ _).trans (_root_.congrArg _ (b.2 n))))))), IsCan t c x → G.rigToExt x = 0 → c ∈ PrimitiveSubmodule A := by
  first | exact @GlobalTheory.PtExt.mem_F1prim_of_rigToExt_eq_zero_of_pow_eq_zero | exact GlobalTheory.PtExt.mem_F1prim_of_rigToExt_eq_zero_of_pow_eq_zero | (intros; apply GlobalTheory.PtExt.mem_F1prim_of_rigToExt_eq_zero_of_pow_eq_zero <;> assumption)
