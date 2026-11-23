module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GenFinSt
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GenFinLocB
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GenFinLocC
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.Linter.Style

-- Source module: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GenFinLocD

section

@[expose] public section

noncomputable section

set_option linter.style.haveILetI false

open Matrix

namespace PositivityTheory.Rg.Sw.Glob.GenFinLocAH

variable {R : Type} [CommRing R] {n : ℕ}

theorem uni_blocks (σ : R →+* R) (h : Matrix (Fin (n + n)) (Fin (n + n)) R) (hu : Uni σ h) :
    Formalism.UG.cT σ (bf h).toBlocks₂₂ * (bf h).toBlocks₁₁ - Formalism.UG.cT σ (bf h).toBlocks₁₂ * (bf h).toBlocks₂₁ = 1 ∧
      Formalism.UG.cT σ (bf h).toBlocks₂₂ * (bf h).toBlocks₁₂ = Formalism.UG.cT σ (bf h).toBlocks₁₂ * (bf h).toBlocks₂₂ := by
  have e := congrArg bf hu
  unfold J2 at e
  rw [bf_mul, bf_mul, bf_cT, block_matrix_to_fromBlocks, ← fromBlocks_toBlocks (bf h), cT_fromBlocks, fromBlocks_multiply,
    fromBlocks_multiply] at e
  simp only [toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂,
    Matrix.mul_zero, Matrix.mul_one, Matrix.mul_neg, Matrix.neg_mul, add_zero, zero_add] at e
  obtain ⟨-, -, e3, e4⟩ := fromBlocks_inj.1 e
  refine ⟨?_, ?_⟩
  · have : -(Formalism.UG.cT σ (bf h).toBlocks₂₂ * (bf h).toBlocks₁₁) + Formalism.UG.cT σ (bf h).toBlocks₁₂ * (bf h).toBlocks₂₁ = -1 := e3
    rw [← neg_neg (1 : Matrix (Fin n) (Fin n) R), ← this]; abel
  · have : -(Formalism.UG.cT σ (bf h).toBlocks₂₂ * (bf h).toBlocks₁₂) + Formalism.UG.cT σ (bf h).toBlocks₁₂ * (bf h).toBlocks₂₂ = 0 := e4
    rw [neg_add_eq_zero] at this; exact this

theorem schur {K : Type} [CommRing K] (P Q A B C D : Matrix (Fin n) (Fin n) K) (h1 : P * A - Q * C = 1) (h2 : P * B = Q * D)
    (hD : IsUnit D.det) : IsUnit P.det := by
  have hQ : Q = P * B * D⁻¹ := by rw [h2, Matrix.mul_assoc, mul_nonsing_inv _ hD, Matrix.mul_one]
  have : P * (A - B * D⁻¹ * C) = 1 := by
    rw [← h1, hQ]; simp only [Matrix.mul_sub, Matrix.mul_assoc]
  have hd := congrArg Matrix.det this
  rw [det_mul, det_one] at hd
  exact ⟨⟨_, _, hd, by rw [mul_comm]; exact hd⟩, rfl⟩

theorem lift2 (σ : R →+* R) (hσ : ∀ x, σ (σ x) = x) (𝔪 : Ideal R) [h𝔪 : 𝔪.IsMaximal] (hne : 𝔪.comap σ ≠ 𝔪)
    (s t : R ⧸ 𝔪) : ∃ x : R, Ideal.Quotient.mk 𝔪 x = s ∧ Ideal.Quotient.mk 𝔪 (σ x) = t := by
  have hsurj : Function.Surjective σ := fun y => ⟨σ y, hσ y⟩
  have h' : (𝔪.comap σ).IsMaximal := Ideal.comap_isMaximal_of_surjective σ hsurj
  have hsup : 𝔪 ⊔ 𝔪.comap σ = ⊤ := Ideal.IsMaximal.coprime_of_ne h𝔪 h' (Ne.symm hne)
  have h1 : (1 : R) ∈ 𝔪 ⊔ 𝔪.comap σ := hsup ▸ Submodule.mem_top
  obtain ⟨e, he, f, hf, hef⟩ := Submodule.mem_sup.1 h1
  obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective s
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective t
  have hf' : σ f ∈ 𝔪 := hf
  have he0 : Ideal.Quotient.mk 𝔪 e = 0 := Ideal.Quotient.eq_zero_iff_mem.2 he
  have hf1 : Ideal.Quotient.mk 𝔪 f = 1 := by
    rw [show f = 1 - e by rw [← hef]; ring, map_sub, map_one, he0, sub_zero]
  have hsf : Ideal.Quotient.mk 𝔪 (σ f) = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hf'
  have hse : Ideal.Quotient.mk 𝔪 (σ e) = 1 := by
    rw [show e = 1 - f by rw [← hef]; ring, map_sub, map_one, map_sub, map_one, hsf, sub_zero]
  refine ⟨u * f + σ y * e, ?_, ?_⟩
  · rw [map_add (f := _), map_mul, map_mul, hf1, he0]; ring
  · rw [map_add (f := _), map_mul, map_mul, map_add (f := _), map_mul, map_mul, hσ, hsf, hse]; ring

theorem caseB (hS : LocRedSplit) (σ : R →+* R) (hσ : ∀ a, σ (σ a) = a) (𝔪 : Ideal R) [h𝔪 : 𝔪.IsMaximal]
    (hne : 𝔪.comap σ ≠ 𝔪) (horb : ∀ 𝔫 : Ideal R, 𝔫.IsMaximal → 𝔫 = 𝔪 ∨ 𝔫 = 𝔪.comap σ)
    (g : Matrix (Fin (n + n)) (Fin (n + n)) R) (hg : Uni σ g) (hgu : IsUnit g.det) :
    ∃ (a : Matrix (Fin n) (Fin n) R) (I : Finset (Fin n)), IsUnit a.det ∧
      IsUnit (blkDm (g * GlobalTheory.StdUnn.blk4 a 0 0 (Formalism.UG.cT σ a)⁻¹ * wIm I)).det := by
  letI : Field (R ⧸ 𝔪) := Ideal.Quotient.field 𝔪
  have hdet : IsUnit (g.map (Ideal.Quotient.mk 𝔪)).det := by rw [← det_map]; exact hgu.map _
  obtain ⟨ab, db, I, hI⟩ := hS (R ⧸ 𝔪) n (Matrix.nonsingInvUnit _ hdet)
  choose x hx using fun i j => lift2 σ hσ 𝔪 hne ((ab : Matrix (Fin n) (Fin n) (R ⧸ 𝔪)) i j)
    (((db⁻¹ : GL (Fin n) (R ⧸ 𝔪)) : Matrix (Fin n) (Fin n) (R ⧸ 𝔪)) j i)
  let a : Matrix (Fin n) (Fin n) R := Matrix.of fun i j => x i j
  have ha1 : a.map (Ideal.Quotient.mk 𝔪) = ab := by ext i j; exact (hx i j).1
  have ha2 : (Formalism.UG.cT σ a).map (Ideal.Quotient.mk 𝔪) = ((db⁻¹ : GL (Fin n) (R ⧸ 𝔪)) : Matrix (Fin n) (Fin n) (R ⧸ 𝔪)) := by
    ext i j; exact (hx j i).2
  have hab : IsUnit (ab : Matrix (Fin n) (Fin n) (R ⧸ 𝔪)).det := Matrix.isUnits_det_units ab
  have hdb : IsUnit ((db⁻¹ : GL (Fin n) (R ⧸ 𝔪)) : Matrix (Fin n) (Fin n) (R ⧸ 𝔪)).det := Matrix.isUnits_det_units _
  have hadet : IsUnit a.det := by
    refine isUnit_of σ 𝔪 horb _ ?_ ?_
    · intro hm
      have h0 := Ideal.Quotient.eq_zero_iff_mem.2 hm
      rw [det_map, ha1] at h0
      exact hab.ne_zero h0
    · intro hm
      have h0 := Ideal.Quotient.eq_zero_iff_mem.2 hm
      rw [← det_cT, det_map, ha2] at h0
      exact hdb.ne_zero h0
  have hca : IsUnit (Formalism.UG.cT σ a).det := by rw [det_cT]; exact hadet.map σ
  have hinv : ((Formalism.UG.cT σ a)⁻¹).map (Ideal.Quotient.mk 𝔪) = (db : Matrix (Fin n) (Fin n) (R ⧸ 𝔪)) := by
    rw [map_nonsing_inv _ _ hca, ha2, Matrix.coe_units_inv, Matrix.nonsing_inv_nonsing_inv _ (Matrix.isUnits_det_units db)]
  set h := g * GlobalTheory.StdUnn.blk4 a 0 0 (Formalism.UG.cT σ a)⁻¹ * wIm I with hh
  have hmap : h.map (Ideal.Quotient.mk 𝔪) =
      g.map (Ideal.Quotient.mk 𝔪) * GlobalTheory.StdUnn.blk4 (ab : Matrix (Fin n) (Fin n) (R ⧸ 𝔪)) 0 0 db * wIm I := by
    rw [hh, Matrix.map_mul, Matrix.map_mul, block_matrix_map, ha1, hinv, wIm_map, Matrix.map_zero _ (map_zero _)]
  have hδ : IsUnit ((blkDm h).map (Ideal.Quotient.mk 𝔪)).det := by rw [blkDm_map, hmap]; exact hI
  refine ⟨a, I, hadet, isUnit_of σ 𝔪 horb _ ?_ ?_⟩
  · intro hm
    have h0 := Ideal.Quotient.eq_zero_iff_mem.2 hm
    rw [det_map] at h0
    exact hδ.ne_zero h0
  · have hu : Uni σ h := (hg.mul (uni_levi σ hσ a hadet)).mul (uni_wIm σ I)
    obtain ⟨e1, e2⟩ := uni_blocks σ h hu
    have hπσ : ∀ y : Matrix (Fin n) (Fin n) R, (Formalism.UG.cT σ y).map (Ideal.Quotient.mk 𝔪) =
        (Formalism.UG.cT σ y).map (Ideal.Quotient.mk 𝔪) := fun _ => rfl
    have e1' := congrArg (fun M => M.map (Ideal.Quotient.mk 𝔪)) e1
    have e2' := congrArg (fun M => M.map (Ideal.Quotient.mk 𝔪)) e2
    simp only [Matrix.map_sub _ (map_sub _), Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at e1' e2'
    have hD : IsUnit ((bf h).toBlocks₂₂.map (Ideal.Quotient.mk 𝔪)).det := hδ
    have hP := schur _ _ _ _ _ _ e1' e2' hD
    intro hm
    have h0 := Ideal.Quotient.eq_zero_iff_mem.2 hm
    rw [blkDm_eq, ← det_cT, det_map] at h0
    exact hP.ne_zero h0

end PositivityTheory.Rg.Sw.Glob.GenFinLocAH
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.IntegralUnitCoefficients.CompFinSigR

section

@[expose] public section

noncomputable section

open scoped Matrix TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta GlobalTheory.AdelicU GlobalTheory.StdUnn IsDedekindDomain NumberField

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.GenFinLocHf

open PositivityTheory.Rg.Sw.Glob.GenFinLocAH

theorem locRing (hF : LocRedField) (hS : LocRedSplit) {R : Type} [CommRing R] {n : ℕ} (σ : R →+* R)
    (hσ : ∀ a, σ (σ a) = a) (𝔪 : Ideal R) (h𝔪 : 𝔪.IsMaximal)
    (horb : ∀ 𝔫 : Ideal R, 𝔫.IsMaximal → 𝔫 = 𝔪 ∨ 𝔫 = 𝔪.comap σ)
    (g : Matrix (Fin (n + n)) (Fin (n + n)) R) (hg : Uni σ g) (hgu : IsUnit g.det) :
    ∃ (a : Matrix (Fin n) (Fin n) R) (I : Finset (Fin n)), IsUnit a.det ∧
      IsUnit (blkDm (g * GlobalTheory.StdUnn.blk4 a 0 0 (Formalism.UG.cT σ a)⁻¹ * wIm I)).det := by
  by_cases hfix : 𝔪.comap σ = 𝔪
  · obtain ⟨I, hI⟩ := caseA hF σ hσ 𝔪 hfix horb g hg hgu
    refine ⟨1, I, by simp, ?_⟩
    have e : GlobalTheory.StdUnn.blk4 (1 : Matrix (Fin n) (Fin n) R) 0 0 (Formalism.UG.cT σ 1)⁻¹ = 1 := by
      rw [Formalism.UG.cT_one, inv_one, block_matrix_one]
    rwa [e, Matrix.mul_one]
  · exact caseB hS σ hσ 𝔪 hfix horb g hg hgu

variable {D : D7} {n : ℕ}

theorem compAt_eq (v : GlobalTheory.FinPl.Pl D) : GlobalTheory.FinPl.compAt D v = compFin D.host.F D.host.E v := by
  apply RingHom.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => rw [RingHom.map_zero, RingHom.map_zero]
  | tmul a e => rfl
  | add x y hx hy => rw [RingHom.map_add (f := _), RingHom.map_add (f := _), hx, hy]

theorem proj_mat (k : G D n) (v : GlobalTheory.FinPl.Pl D) :
    ((matHom _ D.sp.cm.sig (Jst D n) (proj D.sp.cm.sig (Jst D n) v k)).1 :
      Matrix (Fin (n + n)) (Fin (n + n)) (Ev D v)) = (mat k).map (GlobalTheory.FinPl.compAt D v) := by
  rw [compAt_eq]; rfl

theorem int_of_K (k : G D n) (hk : k ∈ K D n) (v : GlobalTheory.FinPl.Pl D) (i j : Fin (n + n)) :
    (mat k).map (GlobalTheory.FinPl.compAt D v) i j ∈ intLoc D.host.F D.host.E v := by
  have hk' : k ∈ levelAll D.sp.cm.sig (Jst D n) (stdLattice D.host.E (n + n)) 1 := hk
  have h := (mem_levelAll.1 hk').1 v
  have hy : (Pi.single j 1 : Fin (n + n) → Ev D v) ∈ latLoc D.host.F (stdLattice D.host.E (n + n)) v := by
    rw [mem_latLoc_stdLattice]
    intro i'
    by_cases hij : i' = j
    · subst hij; simp only [Pi.single_eq_same]; exact one_mem _
    · simp only [Pi.single_eq_of_ne hij]; exact zero_mem _
  have h2 := (mem_stabLoc.1 h _).1 hy
  rw [mem_latLoc_stdLattice] at h2
  have h3 := h2 i
  rw [proj_mat, Matrix.mulVec_single_one] at h3
  exact h3

end PositivityTheory.Rg.Sw.Glob.GenFinLocHf

namespace PositivityTheory.Rg.Sw.Glob.GenFinLocHf

open PositivityTheory.Rg.Sw.Glob.GenFinLocAH

variable {D : D7} {n : ℕ}

theorem sig_apply (x : D.host.E) : D.sp.cm.sig x = star x := rfl

theorem sig_sig (x : D.host.E) : D.sp.cm.sig (D.sp.cm.sig x) = x := by
  rw [sig_apply, sig_apply, star_star]

theorem sig_fix (x : D.host.E) : D.sp.cm.sig x = x ↔ x ∈ (algebraMap D.host.F D.host.E).range := by
  rw [sig_apply]; exact D.sp.cm.fixed x

theorem compFin_sigR (v : GlobalTheory.FinPl.Pl D) (x : AE D) :
    compFin D.host.F D.host.E v (sigR (AF D.host.F) D.sp.cm.sig x) = sigR (Fv D.host.F v) D.sp.cm.sig (compFin D.host.F D.host.E v x) := by
  induction x using TensorProduct.induction_on with
  | zero => rw [RingHom.map_zero, RingHom.map_zero, RingHom.map_zero]
  | tmul a e => rfl
  | add x y hx hy => rw [RingHom.map_add (f := _), RingHom.map_add (f := _), RingHom.map_add (f := _), RingHom.map_add (f := _), hx, hy]

theorem JR_Jst_map (v : GlobalTheory.FinPl.Pl D) :
    (JR (AF D.host.F) (Jst D n)).map (compFin D.host.F D.host.E v) = J2 (Ev D v) n := by
  have h1 : (JR (AF D.host.F) (Jst D n)).map (compFin D.host.F D.host.E v) = (Jst D n).map (inclR (Fv D.host.F v)) := by
    ext i j
    simp only [JR, Matrix.map_apply]
    show compFin D.host.F D.host.E v ((1 : AF D.host.F) ⊗ₜ[D.host.F] _) = (1 : Fv D.host.F v) ⊗ₜ[D.host.F] _
    simp [compFin]
  rw [h1, Jst, block_matrix_map]
  unfold J2
  rw [Matrix.map_zero _ (map_zero _), Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_neg _ (map_neg _),
    Matrix.map_one _ (map_zero _) (map_one _)]

theorem uni_comp (k : G D n) (v : GlobalTheory.FinPl.Pl D) :
    Formalism.UG.cT (sigR (Fv D.host.F v) D.sp.cm.sig) ((mat k).map (GlobalTheory.FinPl.compAt D v)) * J2 (Ev D v) n *
      (mat k).map (GlobalTheory.FinPl.compAt D v) = J2 (Ev D v) n := by
  have hk : Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) (mat k) * JR (AF D.host.F) (Jst D n) * mat k =
      JR (AF D.host.F) (Jst D n) := k.2
  have e := congrArg (fun M => M.map (compFin D.host.F D.host.E v)) hk
  simp only [Matrix.map_mul] at e
  rw [cT_map _ _ _ (compFin_sigR v), JR_Jst_map] at e
  rw [compAt_eq]; exact e

end PositivityTheory.Rg.Sw.Glob.GenFinLocHf

namespace PositivityTheory.Rg.Sw.Glob.GenFinLocHf

open PositivityTheory.Rg.Sw.Glob.GenFinLocAH

theorem unit_sub {S : Type} [CommRing S] (O : Subring S) (z : O) (hz : IsUnit z) : (z : S) ∈ O ∧ ∃ z' ∈ O, (z : S) * z' = 1 := by
  obtain ⟨u, rfl⟩ := hz
  exact ⟨(u : O).2, _, (u⁻¹ : Oˣ).1.2, congrArg Subtype.val u.mul_inv⟩

theorem locSub (hF : LocRedField) (hS : LocRedSplit) {S : Type} [CommRing S] {n : ℕ} (O : Subring S) (τ : S →+* S) (σ : O →+* O)
    (hσ : ∀ a, σ (σ a) = a) (hc : ∀ x, O.subtype (σ x) = τ (O.subtype x)) (𝔪 : Ideal O) (h𝔪 : 𝔪.IsMaximal)
    (horb : ∀ 𝔫 : Ideal O, 𝔫.IsMaximal → 𝔫 = 𝔪 ∨ 𝔫 = 𝔪.comap σ) (M M' : Matrix (Fin (n + n)) (Fin (n + n)) S)
    (hM : ∀ i j, M i j ∈ O) (hM' : ∀ i j, M' i j ∈ O) (hMM : M * M' = 1) (hU : Formalism.UG.cT τ M * J2 S n * M = J2 S n) :
    ∃ (a : Matrix (Fin n) (Fin n) S) (I : Finset (Fin n)), (∀ i j, a i j ∈ O) ∧ (a.det ∈ O ∧ ∃ z' ∈ O, a.det * z' = 1) ∧
      ((blkDm (M * GlobalTheory.StdUnn.blk4 a 0 0 ((a.map τ).transpose)⁻¹ * wIm I)).det ∈ O ∧
        ∃ z' ∈ O, (blkDm (M * GlobalTheory.StdUnn.blk4 a 0 0 ((a.map τ).transpose)⁻¹ * wIm I)).det * z' = 1) := by
  obtain ⟨g, rfl⟩ : ∃ g : Matrix (Fin (n + n)) (Fin (n + n)) O, g.map O.subtype = M :=
    ⟨Matrix.of fun i j => ⟨M i j, hM i j⟩, by ext i j; rfl⟩
  obtain ⟨g', rfl⟩ : ∃ g : Matrix (Fin (n + n)) (Fin (n + n)) O, g.map O.subtype = M' :=
    ⟨Matrix.of fun i j => ⟨M' i j, hM' i j⟩, by ext i j; rfl⟩
  have hinj : Function.Injective (fun M : Matrix (Fin (n + n)) (Fin (n + n)) O => M.map O.subtype) :=
    Matrix.map_injective Subtype.val_injective
  have hUni : Uni σ g := by
    apply hinj
    change (Formalism.UG.cT σ g * J2 O n * g).map O.subtype = (J2 O n).map O.subtype
    rw [Matrix.map_mul, Matrix.map_mul, cT_map _ _ _ hc, standard_symplectic_matrix_map]
    exact hU
  have hdet : IsUnit g.det := by
    have e : g * g' = 1 := by
      apply hinj
      show (g * g').map O.subtype = (1 : Matrix (Fin (n + n)) (Fin (n + n)) O).map O.subtype
      rw [Matrix.map_mul, hMM, Matrix.map_one _ (map_zero _) (map_one _)]
    have e' := congrArg Matrix.det e
    rw [Matrix.det_mul, Matrix.det_one] at e'
    exact ⟨⟨_, _, e', by rw [mul_comm]; exact e'⟩, rfl⟩
  obtain ⟨a, I, ha, hδ⟩ := locRing hF hS σ hσ 𝔪 h𝔪 horb g hUni hdet
  have hca : IsUnit (Formalism.UG.cT σ a).det := by rw [det_cT]; exact ha.map _
  refine ⟨a.map O.subtype, I, fun i j => (a i j).2, ?_, ?_⟩
  · rw [← det_map O.subtype a]; exact unit_sub O a.det ha
  · have e : blkDm (g.map O.subtype * GlobalTheory.StdUnn.blk4 (a.map O.subtype) 0 0 (((a.map O.subtype).map τ).transpose)⁻¹ * wIm I) =
        (blkDm (g * GlobalTheory.StdUnn.blk4 a 0 0 (Formalism.UG.cT σ a)⁻¹ * wIm I)).map O.subtype := by
      rw [blkDm_map, Matrix.map_mul, Matrix.map_mul, block_matrix_map, wIm_map, map_nonsing_inv O.subtype _ hca, cT_map _ _ _ hc a,
        Matrix.map_zero _ (map_zero O.subtype)]
      rfl
    rw [e, ← det_map O.subtype]
    exact unit_sub O _ hδ

end PositivityTheory.Rg.Sw.Glob.GenFinLocHf
end
end
end
