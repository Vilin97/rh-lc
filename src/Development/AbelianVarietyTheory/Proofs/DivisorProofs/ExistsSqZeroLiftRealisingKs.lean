module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrysActApply
public import Development.AbelianVarietyTheory.Definitions.Divisors.InfUniv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumProjSingle
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrystallinePull2SumCup
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsArtinianRingTsze
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystalGluedHodgeGraphFiltrationHasComplement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystalGluedHodgeGraphFiltrationIsotropicPolarisStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystalGluedHodgeGraphFiltrationLieConditionStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystalGluedHodgeGraphFiltrationOrderStable
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CanonicalOfAbelianDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorExistsLiftOrderActionHodgeSummandStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorExistsPolarisationBundleLiftStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLieMultiplicitySquareZeroLiftStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLiftLieOfHodgeSummandLieStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorPrimeToPLevelLiftSquareZeroStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.InfUniv
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemHodgeFiltrationIffReductionGluedFilHtObject

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystalGluedHodgeGraphFiltrationHasComplementStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

theorem _root_.GlobalTheory.T.crystalGluedHodgeGraphFiltration_hasComplement : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t) (β : R →+* k), t = spMap β → ∀ φ : LinearMap.BilinForm k (HdR o₀.A), GlobalTheory.AbDual.IsCorrForm (dp0 k) (𝟙 _) o₀.A o₀.A o₀.P φ → ∀ (d : ℕ) (f : Fin d → (HdR o₀.A →ₗ[k] HdR o₀.A)), (∀ j, IsKS (GlobalTheory.HTCount.crysAct o₀) φ (Fil o₀.A) (GlobalTheory.HTCount.lieZ o₀ β) (f j)) → (∃ M : Submodule (TrivSqZeroExt k (Fin d → k)) (Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) o₀.A), IsCompl (GlobalTheory.HTGlue.glueFil o₀.A f) M) := by
  first | (exact @GlobalTheory.HTGlue.glueFil_hasCompl) | (exact GlobalTheory.HTGlue.glueFil_hasCompl) | (intros; apply GlobalTheory.HTGlue.glueFil_hasCompl  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystalGluedHodgeGraphFiltrationOrderStableStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

theorem _root_.GlobalTheory.T.crystalGluedHodgeGraphFiltration_order_stable : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t) (β : R →+* k), t = spMap β → ∀ φ : LinearMap.BilinForm k (HdR o₀.A), GlobalTheory.AbDual.IsCorrForm (dp0 k) (𝟙 _) o₀.A o₀.A o₀.P φ → ∀ (d : ℕ) (f : Fin d → (HdR o₀.A →ₗ[k] HdR o₀.A)), (∀ j, IsKS (GlobalTheory.HTCount.crysAct o₀) φ (Fil o₀.A) (GlobalTheory.HTCount.lieZ o₀ β) (f j)) → (∀ (c : D.O), ∀ e ∈ (GlobalTheory.HTGlue.glueFil o₀.A f), (haveI := o₀.act.hom (c); push (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) (o₀.act.act (c)) (e)) ∈ (GlobalTheory.HTGlue.glueFil o₀.A f)) := by
  first | exact @GlobalTheory.HTGlue.push_mem_glueFil | exact GlobalTheory.HTGlue.push_mem_glueFil | (intros; apply GlobalTheory.HTGlue.push_mem_glueFil <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorExistsSquareZeroLiftOfFiltration

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

noncomputable section

namespace GlobalTheory.UPel.HT

theorem exists_sqZero_lift_of_fil : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), N.Coprime p → ∀ (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → ∀ (hsq : RingHom.ker π ^ 2 = 0) (tR : R →+* C) (t : Sp C ⟶ Sp R) (t₀ : Sp C₀ ⟶ Sp R), t = spMap tR → t₀ = spMap π ≫ t → ∀ (o₀ : GlobalTheory.UPel.HT.Obj b N t₀) (E : Submodule C (Crys (divided₂ hsq) (spMap π) o₀.A)), (∃ M : Submodule C (Crys (divided₂ hsq) (spMap π) o₀.A), IsCompl E M) → (∀ y : HdR o₀.A, y ∈ Fil o₀.A ↔ ∃ e ∈ E, (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ hsq) rfl o₀.A).Corr e y) → (∀ (c : D.O), ∀ e ∈ E, (haveI := o₀.act.hom (c); push (divided₂ hsq) (spMap π) (o₀.act.act (c)) (e)) ∈ E) → (∀ Φ : Crys (divided₂ hsq) (spMap π) o₀.A →ₗ[C] Crys (divided₂ hsq) (spMap π) o₀.A →ₗ[C] C, GlobalTheory.AbDual.IsCorrForm (divided₂ hsq) (spMap π) o₀.A o₀.A o₀.P Φ → ∀ x ∈ E, ∀ y ∈ E, Φ x y = 0) → (∀ e : Crys (divided₂ hsq) (spMap π) o₀.A, (haveI := o₀.act.hom (algebraMap (𝓞 D.F) D.O D.ω); push (divided₂ hsq) (spMap π) (o₀.act.act (algebraMap (𝓞 D.F) D.O D.ω)) (e)) - tR b.ρ • e ∈ E → ∃ w : Fin D.a → Crys (divided₂ hsq) (spMap π) o₀.A, (∀ i (c : 𝓞 D.F), (haveI := o₀.act.hom (algebraMap (𝓞 D.F) D.O c); push (divided₂ hsq) (spMap π) (o₀.act.act (algebraMap (𝓞 D.F) D.O c)) (w i)) - tR (b.t i c) • w i ∈ E) ∧ e - ∑ i, w i ∈ E) → ∃ (o : GlobalTheory.UPel.HT.Obj b N t) (m : GlobalTheory.UPel.HT.ObjMap o₀ o (spMap π)), liftFil (divided₂ hsq) m.cart = E := by
  intro p _ D R _ b N hN C C₀ _ _ _ _ π hπ hsq tR t t₀ ht ht₀
  subst ht₀
  subst ht
  intro o₀ E hEc hEf hEs hEi hEl
  obtain ⟨A, _, i, h, act, hA, hE, hact⟩ := GlobalTheory.T.harrisTaylor_exists_lift_orderAction_hodge_summand p D R b N C C₀ π hπ hsq tR o₀ E hEc hEf hEs
  haveI : IsCommMonObj A := hA.comm
  subst hE
  obtain ⟨P, φ₂, hP, r1, r2, hsym, hamp, hker, hros, hsq2, hpol⟩ :=
    GlobalTheory.T.harrisTaylor_exists_polarisation_bundle_lift p D R b N C C₀ π hπ hsq tR o₀ A i h hA act hact hEi
  obtain ⟨eta, e1, e2, e3, e4, e5⟩ := GlobalTheory.T.harrisTaylor_primeToP_level_lift_squareZero p D R b N C C₀ π hπ hsq tR o₀ A i h hA act hact hN P φ₂ hP hsq2 hpol
  exact ⟨{ A := A
           ab := hA
           act := act
           P := P
           isLB := hP
           rig₁ := r1
           rig₂ := r2
           symm := hsym
           ample := hamp
           kerP := hker
           rosati := hros
           lie := fun R' _ β x hx v hv => GlobalTheory.T.harrisTaylor_lift_lie_of_hodge_summand_lie p D R b N C C₀ π hπ hsq tR o₀ A i h hA act hact hEl R' β x hx v hv
           lieRank := fun k _ _ x β hx j => GlobalTheory.T.harrisTaylor_lieMultiplicity_squareZeroLift p D R b N C C₀ π hπ hsq tR o₀ A i h act hact k x β hx j
           eta := eta
           eta_add := e1
           eta_lin := e2
           eta_ker := e3
           geom := e4 },
    { φ := i
      φ₂ := φ₂
      cart := h
      sq := hsq2
      act := hact
      pol := hpol
      eta := e5 }, rfl⟩

end GlobalTheory.UPel.HT
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorExistsSquareZeroLiftOfFiltrationStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

theorem _root_.GlobalTheory.T.harrisTaylor_exists_squareZero_lift_of_filtration : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), N.Coprime p → ∀ (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → ∀ (hsq : RingHom.ker π ^ 2 = 0) (tR : R →+* C) (t : Sp C ⟶ Sp R) (t₀ : Sp C₀ ⟶ Sp R), t = spMap tR → t₀ = spMap π ≫ t → ∀ (o₀ : GlobalTheory.UPel.HT.Obj b N t₀) (E : Submodule C (Crys (divided₂ hsq) (spMap π) o₀.A)), (∃ M : Submodule C (Crys (divided₂ hsq) (spMap π) o₀.A), IsCompl E M) → (∀ y : HdR o₀.A, y ∈ Fil o₀.A ↔ ∃ e ∈ E, (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ hsq) rfl o₀.A).Corr e y) → (∀ (c : D.O), ∀ e ∈ E, (haveI := o₀.act.hom (c); push (divided₂ hsq) (spMap π) (o₀.act.act (c)) (e)) ∈ E) → (∀ Φ : Crys (divided₂ hsq) (spMap π) o₀.A →ₗ[C] Crys (divided₂ hsq) (spMap π) o₀.A →ₗ[C] C, GlobalTheory.AbDual.IsCorrForm (divided₂ hsq) (spMap π) o₀.A o₀.A o₀.P Φ → ∀ x ∈ E, ∀ y ∈ E, Φ x y = 0) → (∀ e : Crys (divided₂ hsq) (spMap π) o₀.A, (haveI := o₀.act.hom (algebraMap (𝓞 D.F) D.O D.ω); push (divided₂ hsq) (spMap π) (o₀.act.act (algebraMap (𝓞 D.F) D.O D.ω)) (e)) - tR b.ρ • e ∈ E → ∃ w : Fin D.a → Crys (divided₂ hsq) (spMap π) o₀.A, (∀ i (c : 𝓞 D.F), (haveI := o₀.act.hom (algebraMap (𝓞 D.F) D.O c); push (divided₂ hsq) (spMap π) (o₀.act.act (algebraMap (𝓞 D.F) D.O c)) (w i)) - tR (b.t i c) • w i ∈ E) ∧ e - ∑ i, w i ∈ E) → ∃ (o : GlobalTheory.UPel.HT.Obj b N t) (m : GlobalTheory.UPel.HT.ObjMap o₀ o (spMap π)), liftFil (divided₂ hsq) m.cart = E := by
  first | (exact @GlobalTheory.UPel.HT.exists_sqZero_lift_of_fil) | (exact GlobalTheory.UPel.HT.exists_sqZero_lift_of_fil) | (intros; apply GlobalTheory.UPel.HT.exists_sqZero_lift_of_fil <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemHodgeFiltrationIffReductionGluedFilHtObjectStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

theorem _root_.GlobalTheory.T.mem_hodgeFiltration_iff_reduction_gluedFil_htObject : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t) (β : R →+* k), t = spMap β → ∀ φ : LinearMap.BilinForm k (HdR o₀.A), GlobalTheory.AbDual.IsCorrForm (dp0 k) (𝟙 _) o₀.A o₀.A o₀.P φ → ∀ (d : ℕ) (f : Fin d → (HdR o₀.A →ₗ[k] HdR o₀.A)), (∀ j, IsKS (GlobalTheory.HTCount.crysAct o₀) φ (Fil o₀.A) (GlobalTheory.HTCount.lieZ o₀ β) (f j)) → (∀ y : HdR o₀.A, y ∈ Fil o₀.A ↔ ∃ e ∈ (GlobalTheory.HTGlue.glueFil o₀.A f), (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) rfl o₀.A).Corr e y) := by
  first | exact @GlobalTheory.HTGlue.fil_iff_red_glueFil | exact GlobalTheory.HTGlue.fil_iff_red_glueFil | (intros; apply GlobalTheory.HTGlue.fil_iff_red_glueFil <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSqZeroLiftRealisingKs

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham



theorem GlobalTheory.UPel.HT.exists_sqZero_lift_realising_ks : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t) (β : R →+* k), t = spMap β → ∀ φ : LinearMap.BilinForm k (HdR o₀.A), GlobalTheory.AbDual.IsCorrForm (dp0 k) (𝟙 _) o₀.A o₀.A o₀.P φ → ∀ (d : ℕ) (f : Fin d → (HdR o₀.A →ₗ[k] HdR o₀.A)), (∀ j, IsKS (GlobalTheory.HTCount.crysAct o₀) φ (Fil o₀.A) (GlobalTheory.HTCount.lieZ o₀ β) (f j)) → ∃ (o : GlobalTheory.UPel.HT.Obj b N (spMap (algebraMap k (TrivSqZeroExt k (Fin d → k))) ≫ t)) (m : GlobalTheory.UPel.HT.ObjMap o₀ o (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom)), ∀ x ∈ Fil o₀.A, GlobalTheory.FODef.IsFilLiftV m.cart x (LinearMap.pi fun j => f j x) := by
  intro p _ D R _ b N hN hNp k _ _ t o₀ β ht φ hφ d f hf
  haveI := GlobalTheory.HTGlue.isArtinianRing_tsze k d
  have hsurj : Function.Surjective (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom :=
    fun a => ⟨TrivSqZeroExt.inl a, by simp⟩
  have htR : spMap (algebraMap k (TrivSqZeroExt k (Fin d → k))) ≫ t =
      spMap ((algebraMap k (TrivSqZeroExt k (Fin d → k))).comp β) := by
    rw [ht]; exact (GlobalTheory.Cris.spMap_comp _ _).symm
  have ht₀ : t = spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom ≫
      (spMap (algebraMap k (TrivSqZeroExt k (Fin d → k))) ≫ t) := by
    rw [← Category.assoc, ← GlobalTheory.Cris.spMap_comp]
    have : (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom.comp (algebraMap k (TrivSqZeroExt k (Fin d → k))) = RingHom.id k := by
      ext a; simp
    rw [this]
    simp [spMap]
  have h1 := GlobalTheory.T.crystalGluedHodgeGraphFiltration_hasComplement p D R b N hN hNp k t o₀ β ht φ hφ d f hf
  have h2 := GlobalTheory.T.mem_hodgeFiltration_iff_reduction_gluedFil_htObject p D R b N hN hNp k t o₀ β ht φ hφ d f hf
  have h3 := GlobalTheory.T.crystalGluedHodgeGraphFiltration_order_stable p D R b N hN hNp k t o₀ β ht φ hφ d f hf
  have h4 := GlobalTheory.T.crystalGluedHodgeGraphFiltration_isotropic_polarisation p D R b N hN hNp k t o₀ β ht φ hφ d f hf
  have h5 := GlobalTheory.T.crystalGluedHodgeGraphFiltration_lie_condition p D R b N hN hNp k t o₀ β ht φ hφ d f hf
  have key := GlobalTheory.T.harrisTaylor_exists_squareZero_lift_of_filtration p D R b N hNp (TrivSqZeroExt k (Fin d → k)) k
    (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom hsurj (GlobalTheory.FODef.sqZero k (Fin d → k))
    ((algebraMap k (TrivSqZeroExt k (Fin d → k))).comp β) (spMap (algebraMap k (TrivSqZeroExt k (Fin d → k))) ≫ t) t htR ht₀ o₀ (GlobalTheory.HTGlue.glueFil o₀.A f)
  obtain ⟨o, m, hm⟩ := key h1 h2 h3 h4 h5
  refine ⟨o, m, fun x hx => ?_⟩
  obtain ⟨e, he, hce⟩ := GlobalTheory.HTGlue.exists_mem_glueFil o₀.A o₀.ab f hx
  unfold GlobalTheory.FODef.IsFilLiftV
  refine ⟨e, ?_, hce⟩
  rw [hm]; exact he
end
end
