module

public import Formalism.LocalToGlobal.IndefiniteReal.CutPassage3SOfSteps
public import Formalism.LocalToGlobal.IndefiniteReal.InBlock
public import Formalism.LocalToGlobal.IndefiniteReal.CxPassMet
public import Formalism.LocalToGlobal.Divisibility.InertPartitionLePartF
import Formalism.LocalToGlobal.Divisibility.RowLatLemmas
public import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
import Formalism.LocalToGlobal.IndefiniteReal.CxLemmas
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.Divisibility.ProjLemmas
public import Formalism.LocalToGlobal.IndefiniteReal.CxPass
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Tactic.Basify
import Std.Tactic.BVDecide.Normalize.Prop
public import Formalism.LocalToGlobal.IndefiniteReal.CxPassSk
public import Formalism.LocalToGlobal.IndefiniteReal.EqZeroOfMemRangeAdjoint
import Mathlib.Data.Finsupp.Pointwise
import Mathlib.Tactic.ReduceModChar
public import Formalism.LocalToGlobal.IndefiniteReal.RhoSpec
import Formalism.LocalToGlobal.IndefiniteReal.RowGSurj

-- Source module: Formalism.LocalToGlobal.IndefiniteReal.MajorantAtBaseEqInnerOfPackage

section

@[expose] public section

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.IndefR.CxPass

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.L2.GlobalTheoryTheory.DivPassage

section Part3

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty : Type}

theorem mem_part3_iff (B : BlockDat K G Pl0) (D : InertDat3 B I0 Ty) (ℓ : Lvl K G) (Z : Submodule K B.S.Forms)
    (p : Typ3 K Pl0 I0 Ty) (y : Fin (B.dZ ℓ Z) → K) : y ∈ D.part3 ℓ Z p ↔ B.toF ℓ Z y ∈ D.inertTypeEigenspaceSum p := by
  rw [InertDat3.inert_part_eq_comap]; rfl

end Part3

open Formalism.IndefR.CxPass.In

namespace In3

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type} {m : ℕ}
  (I : In3 K G Pl0 I0 Ty T m)

theorem side_lv (b : Bool) :
    lv (faceOf3 I.A3 I.P0 I.ψ0 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) b = I.A3.side3 (I.lvP b) (I.lvψ b) I.X.zs := by
  cases b <;> rfl

theorem pFrames : I.PFrames := by
  intro s h v
  have hW := I.A3.side_well_formed h.ok ⊥ 1 I.X.zs h.stable h.inBlock h.sep
  have hu : IsUnit (frameOf ((prin I.X).gramE I.cg false)).det :=
    gramE_unit' (prin I.X) I.cg false h.h2g.1 (by show (0 : ℝ) < 1; norm_num)
  exact (rowXE_spec (Df := I.A3.side3 ⊥ 1 I.X.zs) hW _ hu I.X.κ h.h4pos.1 (fun j p v => I.X.lam j I.A3.fam3.base3.μ0 p v)
    (fun j p v => h.h4pos.2.1 j _ p v)).1 v

variable {I} in
theorem Z_stable_g {s : ℕ} (h : I.Hyp s) (g : G) :
    I.X.zs.Z I.A.fam.μ0 ≤ (I.X.zs.Z I.A.fam.μ0).comap ((I.A.fam.R I.A.fam.μ0).r g) := fun _ hz =>
  h.stable.1 I.A.fam.μ0 (Sum.inr g) (Submodule.mem_map_of_mem hz)

variable {I} in
theorem toF_rho (hρ : I.PRho) {s : ℕ} (h : I.Hyp s) (g : G) (x : Fin I.Sg.D → K) :
    (I.A.fam.R I.A.fam.μ0).toF (I.A.fam.lvl ⊥ 1) (I.X.zs.Z I.A.fam.μ0) (I.ρf g *ᵥ x) =
      (I.A.fam.R I.A.fam.μ0).r g ((I.A.fam.R I.A.fam.μ0).toF (I.A.fam.lvl ⊥ 1) (I.X.zs.Z I.A.fam.μ0) x) := by
  obtain ⟨y, hty⟩ := exists_toF_act (I.A.fam.R I.A.fam.μ0) h.ok.ok2.conj (h.ok.ok2.what₂ _) I.A.fam.X h.ok.ok2.irr
    (I.X.zs.Z I.A.fam.μ0) (fun g => Z_stable_g h g) g x
  have key : I.iCg (cpt I.A3.fam3.base3.v0.embedding (I.ρf g *ᵥ x)) = I.iCg (cpt I.A3.fam3.base3.v0.embedding y) := by
    rw [(hρ s h).2.2 g x]
    have e1 : I.iCg (cpt I.A3.fam3.base3.v0.embedding x) =
        I.X.Θ I.A.fam.μ0 (I.X.jR I.A.fam.μ0 ((I.A.fam.R I.A.fam.μ0).toF (I.A.fam.lvl ⊥ 1) (I.X.zs.Z I.A.fam.μ0) x)) :=
      iC_cpt I.X I.cg false I.A.fam.μ0 x
    have e2 : I.iCg (cpt I.A3.fam3.base3.v0.embedding y) =
        I.X.Θ I.A.fam.μ0 (I.X.jR I.A.fam.μ0 ((I.A.fam.R I.A.fam.μ0).toF (I.A.fam.lvl ⊥ 1) (I.X.zs.Z I.A.fam.μ0) y)) :=
      iC_cpt I.X I.cg false I.A.fam.μ0 y
    rw [e1, e2]
    erw [hty]
    exact (h.gequiv I.A.fam.μ0 g _).symm
  have hxy := cpt_injective _ (h.h2g.1 key)
  exact (congrArg (fun z => (I.A.fam.R I.A.fam.μ0).toF (I.A.fam.lvl ⊥ 1) (I.X.zs.Z I.A.fam.μ0) z) hxy).trans hty

variable {I} in
theorem wf_lv {s : ℕ} (h : I.Hyp s) (b : Bool) : (lv (faceOf3 I.A3 I.P0 I.ψ0 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) b).WF := by
  rw [side_lv]; exact I.A3.side_well_formed h.ok _ _ _ h.stable h.inBlock h.sep

variable {I} in
theorem wf_g {s : ℕ} (h : I.Hyp s) : (lv (faceOf3 I.A3 ⊥ 1 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) false).WF :=
  I.A3.side_well_formed h.ok ⊥ 1 _ h.stable h.inBlock h.sep


variable {I} in
theorem opAll_comm {s : ℕ} (h : I.Hyp s) (g : G) (k : (I.A3.rowI I.A.fam.μ0).OpIx) :
    Commute ((I.A3.rowI I.A.fam.μ0).opAll k) ((I.A.fam.R I.A.fam.μ0).r g) := by
  rcases k with i | k
  · exact (h.ok.ok2.what₂ _).opG i g
  · exact (h.ok.what₂ _).opG k g

variable {I} in
theorem Jm_parts (hJt : I.PJt) {s : ℕ} (h : I.Hyp s) (b : Bool) (p : I.A3.fam3.base3.Ix)
    (x : Fin ((lv (faceOf3 I.A3 I.P0 I.ψ0 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) b).dQ I.A3.fam3.base3.μ0) → K)
    (hx : x ∈ (lv (faceOf3 I.A3 I.P0 I.ψ0 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) b).Qp I.A3.fam3.base3.μ0 p) :
    I.Jm b *ᵥ x ∈ (lv (faceOf3 I.A3 ⊥ 1 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) false).Qp I.A3.fam3.base3.μ0 p := by
  cases b
  · refine (mem_part3_iff (I.A.fam.R I.A.fam.μ0) (I.A3.rowI I.A.fam.μ0) (I.A.fam.lvl ⊥ 1) (I.X.zs.Z I.A.fam.μ0) p.1 (I.Jm false *ᵥ x)).2 ?_
    have e : (I.A.fam.R I.A.fam.μ0).toF (I.A.fam.lvl ⊥ 1) (I.X.zs.Z I.A.fam.μ0) (I.Jm false *ᵥ x) =
        (I.A.fam.R I.A.fam.μ0).toF (I.A.fam.lvl I.P0 I.ψ0) (I.X.zs.Z I.A.fam.μ0) x := (hJt s h false I.A.fam.μ0).2.1 x
    rw [e]
    exact (mem_part3_iff (I.A.fam.R I.A.fam.μ0) (I.A3.rowI I.A.fam.μ0) (I.A.fam.lvl I.P0 I.ψ0) (I.X.zs.Z I.A.fam.μ0) p.1 x).1 hx
  · refine (mem_part3_iff (I.A.fam.R I.A.fam.μ0) (I.A3.rowI I.A.fam.μ0) (I.A.fam.lvl ⊥ 1) (I.X.zs.Z I.A.fam.μ0) p.1 (I.Jm true *ᵥ x)).2 ?_
    have e : (I.A.fam.R I.A.fam.μ0).toF (I.A.fam.lvl ⊥ 1) (I.X.zs.Z I.A.fam.μ0) (I.Jm true *ᵥ x) =
        (I.A.fam.R I.A.fam.μ0).toF (I.A.fam.lvl I.P1 I.ψ1) (I.X.zs.Z I.A.fam.μ0) x := (hJt s h true I.A.fam.μ0).2.1 x
    rw [e]
    exact (mem_part3_iff (I.A.fam.R I.A.fam.μ0) (I.A3.rowI I.A.fam.μ0) (I.A.fam.lvl I.P1 I.ψ1) (I.X.zs.Z I.A.fam.μ0) p.1 x).1 hx

variable {I} in
theorem quot_lv (hT : TransferS (K := K) (G := G) (Pl0 := Pl0)) (hJt : I.PJt) {s : ℕ} (h : I.Hyp s) (b : Bool)
    (v : InfinitePlace K)
    (x y : Fin ((lv (faceOf3 I.A3 I.P0 I.ψ0 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) b).dQ I.A3.fam3.base3.μ0) → K) :
    Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K _) ((lv (faceOf3 I.A3 I.P0 I.ψ0 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) b).XQ I.A3.fam3.base3.μ0) v x y =
      (((Nat.card (I.lvP b) : ℝ)⁻¹ : ℝ) : ℂ) *
        Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K _) ((lv (faceOf3 I.A3 ⊥ 1 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) false).XQ I.A3.fam3.base3.μ0) v
          (I.Jm b *ᵥ x) (I.Jm b *ᵥ y) := by
  cases b
  · exact hT (I.A.fam.R I.A.fam.μ0) h.ok.ok2.conj (h.ok.ok2.what₂ _) I.A.fam.X h.ok.ok2.irr I.P0 I.ψ0 (I.X.zs.Z I.A.fam.μ0)
      (fun g => Z_stable_g h g) (I.Jm false) (hJt s h false I.A.fam.μ0).2.1 v x y
  · exact hT (I.A.fam.R I.A.fam.μ0) h.ok.ok2.conj (h.ok.ok2.what₂ _) I.A.fam.X h.ok.ok2.irr I.P1 I.ψ1 (I.X.zs.Z I.A.fam.μ0)
      (fun g => Z_stable_g h g) (I.Jm true) (hJt s h true I.A.fam.μ0).2.1 v x y

variable {I} in
theorem majorant_at_base_eq_inner {s : ℕ} (h : I.Hyp s) (x y : Fin I.Sg.D → K) :
    Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin I.Sg.D)) I.Sg.XE I.A3.fam3.base3.v0 x y =
      ⟪I.iCg (cpt I.A3.fam3.base3.v0.embedding x), I.iCg (cpt I.A3.fam3.base3.v0.embedding y)⟫_ℂ := by
  have e := majorant_at_base_eq_scaled_inner (prin I.X) I.cg false (wf_g h) h.h2g.1 (show (0 : ℝ) < 1 by norm_num) h.h4pos.1
    (fun j p v => h.h4pos.2.1 j _ p v) x y
  have e1 : (prin I.X).nP false = 1 := rfl
  rw [e1, inv_one, Complex.ofReal_one, one_mul] at e
  exact e

variable {I} in
theorem majorant_at_base_eq_inner_of_package {s : ℕ} (h : I.Hyp s) (b : Bool) (x y : Fin (I.Sb b).D → K) :
    Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin (I.Sb b).D)) (I.Sb b).XE I.A3.fam3.base3.v0 x y =
      (((I.X.nP b)⁻¹ : ℝ) : ℂ) *
        ⟪I.X.iC I.cr b I.A3.fam3.base3.μ0 (cpt I.A3.fam3.base3.v0.embedding x),
          I.X.iC I.cr b I.A3.fam3.base3.μ0 (cpt I.A3.fam3.base3.v0.embedding y)⟫_ℂ :=
  majorant_at_base_eq_scaled_inner I.X I.cr b (wf_lv h b) (h.h2 b).1 (h.h4pos.2.2 b) h.h4pos.1 (fun j p v => h.h4pos.2.1 j _ p v) x y

variable {I} in
theorem nP_eq_card_lvP {s : ℕ} (h : I.Hyp s) (b : Bool) : I.X.nP b = (Nat.card (I.lvP b) : ℝ) := by
  cases b
  · exact h.np0
  · exact h.np1

theorem pMet_core (hT : TransferS (K := K) (G := G) (Pl0 := Pl0)) (hsc : ∀ {n : ℕ}
    (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (c : ℝ), 0 < c → ∀ (v : InfinitePlace K) (x y : Fin n → K),
      Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin n)) (Formalism.BranchingDeterminantCap.scaleFrame c X) v x y =
        (((c ^ 2)⁻¹ : ℝ) : ℂ) * Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin n)) X v x y)
    (hJt : I.PJt) (hJ : I.PJ) : I.PMet := by
  intro s h b v x y
  have hcard : (0 : ℝ) < (Nat.card (I.lvP b) : ℝ) := by exact_mod_cast Nat.card_pos
  rw [hsc _ _ (Real.sqrt_pos.2 hcard), Real.sq_sqrt hcard.le]
  by_cases hv : v = I.A3.fam3.base3.v0
  · subst hv
    rw [majorant_at_base_eq_inner_of_package h b, majorant_at_base_eq_inner h, nP_eq_card_lvP h b]
    congr 1
    exact (congrArg₂ (fun a c => ⟪a, c⟫_ℂ) ((hJ s h b).1 x) ((hJ s h b).1 y)).symm
  · exact rowXE_map (lv (faceOf3 I.A3 I.P0 I.ψ0 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) b)
      (lv (faceOf3 I.A3 ⊥ 1 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) false) (wf_lv h b) (wf_g h) _
      (gramE_unit' I.X I.cr b (h.h2 b).1 (h.h4pos.2.2 b)) _
      (gramE_unit' (prin I.X) I.cg false h.h2g.1 (by show (0 : ℝ) < 1; norm_num)) I.X.κ h.h4pos.1
      (fun j p v => I.X.lam j I.A3.fam3.base3.μ0 p v) (fun j p v => h.h4pos.2.1 j _ p v) (I.Jm b)
      (fun p x hx => Jm_parts hJt h b p x hx) _ v hv (quot_lv hT hJt h b v) x y

variable {I} in
theorem rho_parts (hρ : I.PRho) {s : ℕ} (h : I.Hyp s) (g : G) (p : I.A3.fam3.base3.Ix)
    (x : Fin ((lv (faceOf3 I.A3 ⊥ 1 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) false).dQ I.A3.fam3.base3.μ0) → K)
    (hx : x ∈ (lv (faceOf3 I.A3 ⊥ 1 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) false).Qp I.A3.fam3.base3.μ0 p) :
    I.ρf g *ᵥ x ∈ (lv (faceOf3 I.A3 ⊥ 1 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) false).Qp I.A3.fam3.base3.μ0 p := by
  have hx' := (mem_part3_iff (I.A.fam.R I.A.fam.μ0) (I.A3.rowI I.A.fam.μ0) (I.A.fam.lvl ⊥ 1) (I.X.zs.Z I.A.fam.μ0) p.1 x).1 hx
  refine (mem_part3_iff (I.A.fam.R I.A.fam.μ0) (I.A3.rowI I.A.fam.μ0) (I.A.fam.lvl ⊥ 1) (I.X.zs.Z I.A.fam.μ0) p.1 (I.ρf g *ᵥ x)).2 ?_
  rw [toF_rho hρ h g x]
  exact Formalism.L2.Col.eigSum_le_comap (fun k => opAll_comm h g k) _ hx'

theorem pUni_core (hI : InvS (K := K) (G := G) (Pl0 := Pl0)) (hρ : I.PRho) : I.PUni := by
  intro s h v g x y
  by_cases hv : v = I.A3.fam3.base3.v0
  · subst hv
    rw [majorant_at_base_eq_inner h, majorant_at_base_eq_inner h]
    exact (congrArg₂ (fun a c => ⟪a, c⟫_ℂ) ((hρ s h).2.2 g x) ((hρ s h).2.2 g y)).trans (h.gunit g _ _)
  · have e := rowXE_map (lv (faceOf3 I.A3 ⊥ 1 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) false)
      (lv (faceOf3 I.A3 ⊥ 1 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) false) (wf_g h) (wf_g h) _
      (gramE_unit' (prin I.X) I.cg false h.h2g.1 (by show (0 : ℝ) < 1; norm_num)) _
      (gramE_unit' (prin I.X) I.cg false h.h2g.1 (by show (0 : ℝ) < 1; norm_num)) I.X.κ h.h4pos.1
      (fun j p v => I.X.lam j I.A3.fam3.base3.μ0 p v) (fun j p v => h.h4pos.2.1 j _ p v) (I.ρf g)
      (fun p x hx => rho_parts hρ h g p x hx) 1 v hv
      (fun x y => by
        rw [one_mul]
        exact (hI (I.A.fam.R I.A.fam.μ0) h.ok.ok2.conj (h.ok.ok2.what₂ _) I.A.fam.X h.ok.ok2.irr (I.X.zs.Z I.A.fam.μ0)
          (fun g => Z_stable_g h g) g (I.ρf g) (toF_rho hρ h g) v x y).symm) x y
    rw [one_mul] at e
    exact e.symm

theorem pMet_of (hJt : I.PJt) (hJ : I.PJ) : I.PMet :=
  I.pMet_core transferS_holds (fun X c hc v x y => BlockMetrics.majAt_scaleFrame X c hc v x y) hJt hJ

theorem pUni_of (_hJt : I.PJt) (hρ : I.PRho) : I.PUni :=
  I.pUni_core invS_holds hρ

end In3

end Formalism.IndefR.CxPass
end
end
end

-- Source module: Formalism.LocalToGlobal.IndefiniteReal.CxPassGood

section

@[expose] public section

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.IndefR.CxPass

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx

namespace GoodPlacesAlt

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G]

theorem sum_chars_eq {S : Type} [Fintype S] {Ws : S → Type} [∀ s, AddCommGroup (Ws s)] [∀ s, Module K (Ws s)]
    (τ : ∀ s, Representation K G (Ws s)) (Xc : Finset (G → K))
    (hinj : ∀ s t, Formalism.IndefR.TransferLatticeStatement.charOf (τ s) = Formalism.IndefR.TransferLatticeStatement.charOf (τ t) → s = t) (hX : CharsX τ Xc)
    {M : Type} [AddCommMonoid M] (F : (G → K) → M) :
    ∑ t, F (Formalism.IndefR.TransferLatticeStatement.charOf (τ t)) = ∑ χ ∈ Xc, F χ := by
  classical
  have himg : Finset.univ.image (fun t => Formalism.IndefR.TransferLatticeStatement.charOf (τ t)) = Xc := by
    ext χ
    rw [hX χ]
    simp
  rw [← himg, Finset.sum_image (fun s _ t _ h => hinj s t h)]

theorem mulVec_sum_smul {n : ℕ} (c : G → K) (M : G → Matrix (Fin n) (Fin n) K) (x : Fin n → K) :
    (∑ g, c g • M g) *ᵥ x = ∑ g, c g • (M g *ᵥ x) := by
  classical
  have key : ∀ s : Finset G, (∑ g ∈ s, c g • M g) *ᵥ x = ∑ g ∈ s, c g • (M g *ᵥ x) := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · simp
    · intro a s ha ih
      rw [Finset.sum_insert ha, Finset.sum_insert ha, Matrix.add_mulVec, ← ih]
      first
        | rw [Matrix.smul_mulVec]
        | rw [Matrix.smul_mulVec_assoc]
        | simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
  exact key Finset.univ

theorem cpt_sum_smul (σ : K →+* ℂ) {n : ℕ} (c : G → K) (y : G → Fin n → K) :
    cpt σ (∑ g, c g • y g) = ∑ g, σ (c g) • cpt σ (y g) := by
  funext i

  simp [cpt, Finset.sum_apply, map_sum]

theorem sum_eq_one_of {E : Type} [AddCommGroup E] [Module ℂ E] (σ : K →+* ℂ) {n : ℕ}
    (f : (Fin n → ℂ) →ₗ[ℂ] E) (hf : Function.Injective f) (ρ : G → Matrix (Fin n) (Fin n) K)
    (act : G → E →ₗ[ℂ] E) (hρ : ∀ g x, f (cpt σ (ρ g *ᵥ x)) = act g (f (cpt σ x)))
    (c : G → K) (hfix : ∀ x, ∑ g, σ (c g) • act g (f (cpt σ x)) = f (cpt σ x)) :
    ∑ g, c g • ρ g = 1 := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro x
  rw [Matrix.toLin'_apply, Matrix.toLin'_one, LinearMap.id_apply]
  have h1 : f (cpt σ ((∑ g, c g • ρ g) *ᵥ x)) = f (cpt σ x) := by

    rw [mulVec_sum_smul, cpt_sum_smul, map_sum]
    simp only [map_smul, hρ]
    exact hfix x
  have h2 := hf h1
  funext i
  exact σ.injective (congrFun h2 i)

end GoodPlacesAlt

namespace In

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {m : ℕ}
  (I : In K G Pl0 T m)

end In

end Formalism.IndefR.CxPass
end
end
end

-- Source module: Formalism.LocalToGlobal.IndefiniteReal.PGoodOfRho

section

@[expose] public section

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.IndefR.CxPass

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx

namespace In3

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type} {m : ℕ}
  (I : In3 K G Pl0 I0 Ty T m)

theorem sum_eMat_eq {S : Type} [Fintype S] {Ws : S → Type} [∀ s, AddCommGroup (Ws s)] [∀ s, Module K (Ws s)]
    (τ : ∀ s, Representation K G (Ws s))
    (hinj : ∀ s t, Formalism.IndefR.TransferLatticeStatement.charOf (τ s) = Formalism.IndefR.TransferLatticeStatement.charOf (τ t) → s = t) (hX : CharsX τ I.A.fam.X) :
    ∑ t, I.eMat (τ t) = ∑ g : G, (idemOf I.A.fam.X).coeff g • I.ρf g := by
  classical
  have hc : ∀ g : G, (idemOf I.A.fam.X).coeff g =
      ∑ χ ∈ I.A.fam.X, χ 1 / (Fintype.card G : K) * χ g⁻¹ := by
    intro g
    simp [idemOf, chiIdem, MonoidAlgebra.coeff_sum, MonoidAlgebra.coeff_single, Finsupp.finsetSum_apply,
      Finsupp.single_apply]
  simp only [eMat]
  rw [GoodPlacesAlt.sum_chars_eq τ I.A.fam.X hinj hX
    (fun χ => (χ 1 / (Fintype.card G : K)) • ∑ x : G, χ x⁻¹ • I.ρf x)]
  simp only [hc, Finset.sum_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]

theorem iCg_cpt (x : Fin ((lv (faceOf3 I.A3 ⊥ 1 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) false).dQ I.A3.fam3.base3.μ0) → K) :
    I.X.iC I.cg false I.A3.fam3.base3.μ0 (cpt I.A3.fam3.base3.v0.embedding x) =
      I.X.Θ I.A3.fam3.base3.μ0 (I.X.jR I.A3.fam3.base3.μ0
        ((I.A.fam.R I.A3.fam3.base3.μ0).toF (I.A.fam.lvl ⊥ 1) (I.X.zs.Z I.A3.fam3.base3.μ0) x)) := by
  rw [CxData.iC_eq_comp, CxData.lin_uQ_cpt]
  rfl

theorem idemOf_fix {s : ℕ} (hok : I.A.fam.Ok s)
    (x : Fin ((I.A.fam.R I.A3.fam3.base3.μ0).dZ (I.A.fam.lvl ⊥ 1) (I.X.zs.Z I.A3.fam3.base3.μ0)) → K) :
    ∑ g : G, (idemOf I.A.fam.X).coeff g •
        (I.A.fam.R I.A3.fam3.base3.μ0).r g ((I.A.fam.R I.A3.fam3.base3.μ0).toF (I.A.fam.lvl ⊥ 1) (I.X.zs.Z I.A3.fam3.base3.μ0) x) =
      (I.A.fam.R I.A3.fam3.base3.μ0).toF (I.A.fam.lvl ⊥ 1) (I.X.zs.Z I.A3.fam3.base3.μ0) x := by
  have hgood : goodAt (I.A.fam.lvl ⊥ 1).X (I.A.fam.lvl ⊥ 1).P (I.A.fam.lvl ⊥ 1).ψ = idemOf I.A.fam.X := by
    show idemOf I.A.fam.X * lvlIdem ⊥ 1 = _
    rw [level_idempotent_bot K G 1, mul_one]
  have hidem : goodAt (I.A.fam.lvl ⊥ 1).X (I.A.fam.lvl ⊥ 1).P (I.A.fam.lvl ⊥ 1).ψ *
      goodAt (I.A.fam.lvl ⊥ 1).X (I.A.fam.lvl ⊥ 1).P (I.A.fam.lvl ⊥ 1).ψ =
      goodAt (I.A.fam.lvl ⊥ 1).X (I.A.fam.lvl ⊥ 1).P (I.A.fam.lvl ⊥ 1).ψ := by
    rw [hgood]
    exact (idempotent_central K G I.A.fam.X hok.irr).1
  have h : (I.A.fam.R I.A3.fam3.base3.μ0).S.gaOp (I.A.fam.R I.A3.fam3.base3.μ0).r
        (goodAt (I.A.fam.lvl ⊥ 1).X (I.A.fam.lvl ⊥ 1).P (I.A.fam.lvl ⊥ 1).ψ)
        ((I.A.fam.R I.A3.fam3.base3.μ0).toF (I.A.fam.lvl ⊥ 1) (I.X.zs.Z I.A3.fam3.base3.μ0) x) =
      (I.A.fam.R I.A3.fam3.base3.μ0).toF (I.A.fam.lvl ⊥ 1) (I.X.zs.Z I.A3.fam3.base3.μ0) x :=
    BlockDat.gaOp_fix (I.A.fam.R I.A3.fam3.base3.μ0) (I.A.fam.lvl ⊥ 1) hidem
      (((I.A.fam.R I.A3.fam3.base3.μ0).zE (I.A.fam.lvl ⊥ 1) (I.X.zs.Z I.A3.fam3.base3.μ0)).mulVec x)
  rw [hgood] at h
  conv_rhs => rw [← h]
  simp only [CSD.gaOp, LinearMap.sum_apply, LinearMap.smul_apply]

theorem iCg_fix {s : ℕ} (hH : I.Hyp s)
    (x : Fin ((lv (faceOf3 I.A3 ⊥ 1 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) false).dQ I.A3.fam3.base3.μ0) → K) :
    ∑ g : G, I.A3.fam3.base3.v0.embedding ((idemOf I.A.fam.X).coeff g) •
        I.gE g (I.X.iC I.cg false I.A3.fam3.base3.μ0 (cpt I.A3.fam3.base3.v0.embedding x)) =
      I.X.iC I.cg false I.A3.fam3.base3.μ0 (cpt I.A3.fam3.base3.v0.embedding x) := by
  have hq : ∀ (g : G) (f : I.A3.fam3.amb3.FR I.A3.fam3.base3.μ0),
      I.gE g (I.X.Θ I.A3.fam3.base3.μ0 (I.X.jR I.A3.fam3.base3.μ0 f)) =
        I.X.Θ I.A3.fam3.base3.μ0 (I.X.jR I.A3.fam3.base3.μ0 ((I.A.fam.R I.A3.fam3.base3.μ0).r g f)) :=
    fun g f => (hH.gequiv I.A3.fam3.base3.μ0 g f).symm
  have hq' : ∀ g : G, I.gE g (I.X.Θ I.A3.fam3.base3.μ0 (I.X.jR I.A3.fam3.base3.μ0
      ((I.A.fam.R I.A3.fam3.base3.μ0).toF (I.A.fam.lvl ⊥ 1) (I.X.zs.Z I.A3.fam3.base3.μ0) x))) =
      I.X.Θ I.A3.fam3.base3.μ0 (I.X.jR I.A3.fam3.base3.μ0 ((I.A.fam.R I.A3.fam3.base3.μ0).r g
        ((I.A.fam.R I.A3.fam3.base3.μ0).toF (I.A.fam.lvl ⊥ 1) (I.X.zs.Z I.A3.fam3.base3.μ0) x))) := fun g => hq g _
  rw [I.iCg_cpt x]
  simp_rw [hq']
  conv_rhs => rw [← I.idemOf_fix hH.ok.ok2 x]
  erw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  erw [LinearMap.map_smulₛₗ, map_smul]
  first | done | rfl

theorem pGood_of_rho (hρ : I.PRho) {S : Type} [Fintype S] {Ws : S → Type} [∀ s, AddCommGroup (Ws s)]
    [∀ s, Module K (Ws s)] (τ : ∀ s, Representation K G (Ws s)) : I.PGood τ := by
  intro s hH hG hX
  rw [I.sum_eMat_eq τ hG.2.2.2 hX]
  obtain ⟨-, -, hρg⟩ := hρ s hH
  exact GoodPlacesAlt.sum_eq_one_of I.A3.fam3.base3.v0.embedding I.iCg hH.h2g.1 I.ρf (fun g => I.gE g) hρg
    (fun g => (idemOf I.A.fam.X).coeff g) (fun x => I.iCg_fix hH x)

theorem pGood_of (_hJt : I.PJt) (hρ : I.PRho) {S : Type} [Fintype S] {Ws : S → Type} [∀ s, AddCommGroup (Ws s)]
    [∀ s, Module K (Ws s)] [∀ s, FiniteDimensional K (Ws s)] (τ : ∀ s, Representation K G (Ws s)) : I.PGood τ := pGood_of_rho I hρ τ

end In3

end Formalism.IndefR.CxPass
end
end
end

-- Source module: Formalism.LocalToGlobal.IndefiniteReal.CutPassage3

section

@[expose] public section

namespace Formalism.IndefR.CxPass

theorem steps3 : Steps3 := fun _ _ _ _ _ _ _ _ _ _ _ _ I =>
  ⟨I.pRho, I.pJ, I.pRange, I.pMet_of I.pJt I.pJ, I.pFrames, I.pUni_of I.pJt I.pRho, I.pLat_of I.pJt,
    I.pGLat_of I.pJt I.pRho, I.pSand_of I.pJt I.pJ I.pRho I.pRange, fun _ _ _ _ _ _ τ => I.pGood_of I.pJt I.pRho τ⟩

theorem cutPassage3S : CutPassage3S := cutPassage3S_of_steps steps3

end Formalism.IndefR.CxPass
end
end
