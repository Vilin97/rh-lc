module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAldCut
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ExistsStandardHermitianSpace
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAldK
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
public import Development.AbelianVarietyTheory.Definitions.Foundations.EqPlaceIdemOfIsPrimeIdem
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsLatticeFrameIsMajorantFrame
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsLocUnit
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
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.IsSingTest
import Development.WeilBound.ThetaLifts.LatticeBasics.Hypotheses2
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalUnitExistence.ExistsLocUnit
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalUnitExistence.ExistsSkewUnit
import Mathlib.Tactic.ReduceModChar
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAldDefs
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalUnitExistence.InclusionFromRowsIdentityZero
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalUnitExistence.DetLast
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalUnitExistence.EpsNegUnit
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalUnitExistence.ExistsEigenvalueGLOneEqCuspidalLabelGen
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalUnitExistence.ExistsLocUnit
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalUnitExistence.IwaTransport
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.LocUnit

section

@[expose] public section

noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem UpperTheory.TP.K.exists_locUnit {B : Base F E} (hB : UpperTheory.TP.W.GoodK σ B) {ξ : E} (hξ : ξ ≠ 0) (hσξ : σ ξ = -ξ) (v : Pl (F := F)) :
    ∃ u : (Fv F v ⊗[F] E)ˣ, (u : Fv F v ⊗[F] E) ∈ intLoc F E v ∧ ((u⁻¹ : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) ∈ intLoc F E v ∧
      sigR (Fv F v) σ (u : Fv F v ⊗[F] E) = -(u : Fv F v ⊗[F] E) :=
  _root_.UpperTheory.Reformulated.B.Gs6.exists_locUnit hB hξ hσξ v

end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilLdexbUnit

section

@[expose] public section



section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Ldexb
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem exists_skewUnit_k {B : Base F E} (hB : _root_.UpperTheory.TP.W.GoodK σ B) :
    ∃ r : (AE F E)ˣ, cA σ (r : AE F E) = -(r : AE F E) ∧
      (∀ v, compFin F E v (r : AE F E) ∈ intLoc F E v ∧ compFin F E v ((r⁻¹ : (AE F E)ˣ) : AE F E) ∈ intLoc F E v) ∧
      ∀ w, ‖piInf (B.emb w) (r : AE F E)‖ = 1 := by
  classical
  have hc := hB.cm
  obtain ⟨ξ, hξ, hσξ⟩ := UnitA.exists_xi hc
  obtain ⟨S, hS⟩ := UnitA.exists_S (F := F) ξ
  choose u hu1 hu2 hu3 using _root_.UpperTheory.TP.K.exists_locUnit hB hξ hσξ
  let xv : ∀ v : Pl F, (Fv F v ⊗[F] E)ˣ := fun v =>
    ⟨inclR (F := F) (Fv F v) ξ, inclR (F := F) (Fv F v) ξ⁻¹, by rw [← map_mul, mul_inv_cancel₀ hξ, map_one],
      by rw [← map_mul, inv_mul_cancel₀ hξ, map_one]⟩
  let b : ∀ v : Pl F, GL (Fin 1) (Fv F v ⊗[F] E) := fun v => if v ∈ S then sc1 (u v * (xv v)⁻¹) else 1
  have hb : ∀ v ∉ S, b v = 1 := fun v hv => if_neg hv
  let e : ∀ w : InfinitePlace F, w.Completion ⊗[F] E ≃+* ℂ := fun w =>
    RingEquiv.ofBijective (infEmb (B.emb w)) (infEmb_bijective hc (B.emb w))
  have hτ : ∀ w : InfinitePlace F, (B.emb w).1 ξ ≠ 0 := fun w => (map_ne_zero _).2 hξ
  let c : ∀ w : InfinitePlace F, GL (Fin 1) (w.Completion ⊗[F] E) := fun w =>
    sc1 (Units.map (e w).symm.toMonoidHom (Units.mk0 (Complex.I / (B.emb w).1 ξ) (div_ne_zero Complex.I_ne_zero (hτ w))))
  obtain ⟨γ, hγf, hγi⟩ := Frames.exists_GL_of_components S b hb c
  let X : (AE F E)ˣ := ⟨inclR (F := F) (AF F) ξ, inclR (F := F) (AF F) ξ⁻¹, by rw [← map_mul, mul_inv_cancel₀ hξ, map_one],
      by rw [← map_mul, inv_mul_cancel₀ hξ, map_one]⟩
  let r : (AE F E)ˣ := Matrix.GeneralLinearGroup.det γ * X
  have hf : ∀ v, Units.map (compFin F E v).toMonoidHom r = if v ∈ S then u v else xv v := by
    intro v
    have hX : Units.map (compFin F E v).toMonoidHom X = xv v := Units.ext (UnitA.compFin_inclR v ξ)
    rw [map_mul, map_det_bc, hγf v, hX]
    by_cases hv : v ∈ S
    · simp only [b, if_pos hv, det_sc1, inv_mul_cancel_right]
    · simp only [b, if_neg hv, map_one, one_mul]
  have hfv : ∀ v, compFin F E v (r : AE F E) = ((if v ∈ S then u v else xv v : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) := by
    intro v; rw [← hf v]; rfl
  have hfi : ∀ v, compFin F E v ((r⁻¹ : (AE F E)ˣ) : AE F E) =
      (((if v ∈ S then u v else xv v : (Fv F v ⊗[F] E)ˣ)⁻¹ : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) := by
    intro v; rw [← hf v, ← map_inv]; rfl
  have hi : ∀ w, infEmb (B.emb w) (compInf F E w (r : AE F E)) = Complex.I := by
    intro w
    have hX : Units.map (compInf F E w).toMonoidHom X = Units.map (inclR (F := F) w.Completion).toMonoidHom (Units.mk0 ξ hξ) :=
      Units.ext (UnitA.compInf_inclR w ξ)
    have h1 : Units.map (compInf F E w).toMonoidHom r = Matrix.GeneralLinearGroup.det (c w) *
        Units.map (inclR (F := F) w.Completion).toMonoidHom (Units.mk0 ξ hξ) := by
      rw [map_mul, map_det_bc, hγi w, hX]
    have h2 : compInf F E w (r : AE F E) = (e w).symm (Complex.I / (B.emb w).1 ξ) * inclR (F := F) w.Completion ξ := by
      have := congrArg Units.val h1
      simpa [c, det_sc1] using this
    rw [h2, map_mul]
    have h3 : infEmb (B.emb w) ((e w).symm (Complex.I / (B.emb w).1 ξ)) = Complex.I / (B.emb w).1 ξ :=
      (e w).apply_symm_apply _
    have h4 : infEmb (B.emb w) (inclR (F := F) w.Completion ξ) = (B.emb w).1 ξ := by
      change infEmb (B.emb w) ((1 : w.Completion) ⊗ₜ[F] ξ) = _
      rw [infEmb_tmul, map_one, one_mul]
    rw [h3, h4, div_mul_cancel₀ _ (hτ w)]
  refine ⟨r, ?_, fun v => ?_, fun w => ?_⟩
  ·
    have key : -(cA σ (r : AE F E) * ((r⁻¹ : (AE F E)ˣ) : AE F E)) = 1 := by
      refine GlobalTheory.AdelicU.Supp.adTens_eq_one' (fun w => ?_) (fun v => ?_)
      · have hz : sigR w.Completion σ (compInf F E w (r : AE F E)) = -compInf F E w (r : AE F E) := by
          apply (e w).injective
          change infEmb (B.emb w) _ = infEmb (B.emb w) _
          rw [← infEmb_sigR hc, hi w, map_neg, hi w, Complex.conj_I]
        have hu : compInf F E w (r : AE F E) * compInf F E w ((r⁻¹ : (AE F E)ˣ) : AE F E) = 1 := by
          rw [← map_mul, Units.mul_inv, map_one]
        rw [map_neg, map_mul, UnitA.compInf_cA, hz, neg_mul, neg_neg, hu]
      · have hz : sigR (Fv F v) σ (compFin F E v (r : AE F E)) = -compFin F E v (r : AE F E) := by
          rw [hfv v]
          by_cases hv : v ∈ S
          · simp only [if_pos hv]; exact hu3 v
          · simp only [if_neg hv, xv]
            rw [UnitA.sigR_inclR, hσξ, map_neg]
        have hu : compFin F E v (r : AE F E) * compFin F E v ((r⁻¹ : (AE F E)ˣ) : AE F E) = 1 := by
          rw [← map_mul, Units.mul_inv, map_one]
        rw [map_neg, map_mul, UnitA.compFin_cA, hz, neg_mul, neg_neg, hu]
    have : cA σ (r : AE F E) * ((r⁻¹ : (AE F E)ˣ) : AE F E) = -1 := by
      rw [← neg_neg (cA σ (r : AE F E) * _), key]
    calc cA σ (r : AE F E) = cA σ (r : AE F E) * ((r⁻¹ : (AE F E)ˣ) : AE F E) * (r : AE F E) := by
          rw [mul_assoc, Units.inv_mul, mul_one]
      _ = -(r : AE F E) := by rw [this, neg_one_mul]
  · rw [hfv v, hfi v]
    by_cases hv : v ∈ S
    · simp only [if_pos hv]; exact ⟨hu1 v, hu2 v⟩
    · simp only [if_neg hv]; exact hS v hv
  · change ‖infEmb (B.emb w) (compInf F E w (r : AE F E))‖ = 1
    rw [hi w, Complex.norm_I]
end PositivityTheory.SiegelWeilFormula.Ldexb
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilLdexbVal

section

@[expose] public section



section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.Ldexb
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem jpar_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} {n : ℕ} (h : n + 1 = d.n) {Y : Spc F E n} {b : GL (Fin n ⊕ Fin n) E} {j : G2 σ Y →* d.G}
    (hJ : _root_.PositivityTheory.SiegelWeilFormula.Ald.IsJ_k d h b j) {p : G2 σ Y} (hp : ParF b p) :
    ParF d.b (j p) ∧ (inFrame d.b (j p)).toBlocks₁₁.det = (inFrame b p).toBlocks₁₁.det := by
  obtain ⟨-, h2, h3⟩ := hJ
  set X := inFrame d.b (j p) with hX
  have hsub : ∀ x y, X (Sum.map (Ald.em0 h) (Ald.em0 h) x) (Sum.map (Ald.em0 h) (Ald.em0 h) y) = inFrame b p x y :=
    fun x y => by rw [← h2 p]; rfl
  have hl : ∀ v, X (Sum.inl (Ald.i0 h)) v = (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) (Sum.inl (Ald.i0 h)) v :=
    fun v => (h3 p _ (by simp) v).1
  have hl' : ∀ v, X v (Sum.inl (Ald.i0 h)) = (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) v (Sum.inl (Ald.i0 h)) :=
    fun v => (h3 p _ (by simp) v).2
  have hr : ∀ v, X (Sum.inr (Ald.i0 h)) v = (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) (Sum.inr (Ald.i0 h)) v :=
    fun v => (h3 p _ (by simp) v).1
  constructor
  · show X.toBlocks₂₁ = 0
    ext a c
    show X (Sum.inr a) (Sum.inl c) = 0
    by_cases ha : a = Ald.i0 h
    · subst ha; rw [hr]; simp [Matrix.one_apply]
    by_cases hc : c = Ald.i0 h
    · subst hc; rw [hl']; simp [Matrix.one_apply]
    obtain ⟨a', rfl⟩ := (Ald.ne_last_iff_mem_range h a).1 ha
    obtain ⟨c', rfl⟩ := (Ald.ne_last_iff_mem_range h c).1 hc
    have e := hsub (Sum.inr a') (Sum.inl c')
    simp only [Sum.map_inr, Sum.map_inl] at e
    rw [e]
    exact congrFun (congrFun hp a') c'
  · rw [det_last h X.toBlocks₁₁ (fun c => by
      show X (Sum.inl (Ald.i0 h)) (Sum.inl c) = _
      rw [hl]; by_cases hc : c = Ald.i0 h
      · subst hc; simp
      · simp [Matrix.one_apply, hc, Ne.symm hc])]
    congr 1
    ext a c
    have e := hsub (Sum.inl a) (Sum.inl c)
    simp only [Sum.map_inl] at e
    exact e
theorem val_pull_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} {n : ℕ} (h : n + 1 = d.n) {Y : Spc F E n} {b : GL (Fin n ⊕ Fin n) E} {j : G2 σ Y →* d.G}
    (hJ : _root_.PositivityTheory.SiegelWeilFormula.Ald.IsJ_k d h b j) (hb : IsFrame2 σ Y b) :
    ∀ (p : G2 σ Y) (t : GL (Fin n) (AE F E)), IsPar p t → ∀ k ∈ d.K.comap j,
      (d.a ∘ j) (p * k) = (absE F E (Matrix.GeneralLinearGroup.det t) : ℝ) := by
  intro p t hpt k hk
  obtain ⟨hpf, hdet⟩ := par_to hb hpt
  obtain ⟨hbig, hdet2⟩ := _root_.PositivityTheory.SiegelWeilFormula.Ldexb.jpar_k h hJ hpf
  obtain ⟨t', ht', hdt'⟩ := par_of d.ok.frame hbig
  show d.a (j (p * k)) = _
  rw [map_mul, d.ok.hgt.val (j p) t' ht' (j k) hk]
  congr 2
  apply Units.ext
  simp only [Matrix.GeneralLinearGroup.val_det_apply]
  rw [hdt', hdet2, hdet]
end PositivityTheory.SiegelWeilFormula.Ldexb
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilLdexbMain

section

@[expose] public section



section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Ldexb
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem hgtPull_k : _root_.PositivityTheory.SiegelWeilFormula.Ald.HgtPull_k := by
  intro F E _ _ _ _ _ σ d n h Y b j hn hs hb hJ
  have hB := d.ok.good
  have hσ : ∀ z, σ (σ z) = z := UnitA.sig_sig hB.cm
  refine ⟨fun x => ?_, _root_.PositivityTheory.SiegelWeilFormula.Ldexb.val_pull_k h hJ hb⟩
  obtain ⟨Y₀, b₀, K₀, a₀, hb₀, he₀, hK₀, ha₀⟩ := _root_.PositivityTheory.SiegelWeilFormula.Ldexb.exists_standard_hermitian_space hB hn
  obtain ⟨ε, he⟩ := hb.1
  have hK : IsStdK (σ := σ) (Y := Y) d.B b (d.K.comap j) := _root_.PositivityTheory.SiegelWeilFormula.Ald.kStd_k F E σ d n h Y b j hb hJ
  rcases hs with ⟨-, hY⟩ | ⟨-, hY⟩
  ·
    have hε : ε = -1 := eps_neg_unit (eps_neg hn hσ hY he)
    subst hε
    obtain ⟨r, hr, hrf, hri⟩ := _root_.PositivityTheory.SiegelWeilFormula.Ldexb.exists_skewUnit_k hB
    refine iwa_transport (B := d.B) hσ hb hb₀ he he₀ r ?_ hrf hri hK₀ ha₀.iwa hK x
    rw [hr]; push_cast; ring
  ·
    have hε : ε = 1 := eps_unit (eps_one hn hσ hY he)
    subst hε
    refine iwa_transport (B := d.B) hσ hb hb₀ he he₀ 1 ?_ (fun v => ?_) (fun w => ?_) hK₀ ha₀.iwa hK x
    · simp
    · simp only [Units.val_one, inv_one, map_one]; exact ⟨one_mem _, one_mem _⟩
    · simp
end PositivityTheory.SiegelWeilFormula.Ldexb
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAldHgt

section

@[expose] public section



section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Ald
theorem hgtPull_k : _root_.PositivityTheory.SiegelWeilFormula.Ald.HgtPull_k := _root_.PositivityTheory.SiegelWeilFormula.Ldexb.hgtPull_k
end PositivityTheory.SiegelWeilFormula.Ald
end
end
end
end
