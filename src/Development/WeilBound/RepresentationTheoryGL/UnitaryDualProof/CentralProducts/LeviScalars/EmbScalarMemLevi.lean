module

public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CentralProducts.TopProdD
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipotentDerivatives.DerUnipLeUnipB
public import GroundTheory.AutomorphicForms.InductionParabolicGroups
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.ColMatMulGlEmbMat
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicTwistedKernelDerivativeZero
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedJacquetPhiMinusEquiv
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RestrictionMirabolicTwistedKernel
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedJacquetPhiMinusEquiv
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.WhittakerCuspidal.UnipBEqUnipotent
public import GroundTheory.AutomorphicForms.AdmissibleFiniteLength
import GroundTheory.AutomorphicForms.AdmissibleInduction
import GroundTheory.AutomorphicForms.CuspidalAdmissible
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DerCharEqOneOfMemUnipRad

section

@[expose] public section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir

noncomputable section

namespace GlobalTheory.CompanionTheory.BZMirJac

section Abstract

variable {M V X Y : Type} [Group M] [AddCommGroup V] [Module ℂ V] [AddCommGroup X] [Module ℂ X]
  [AddCommGroup Y] [Module ℂ Y]

theorem ker_comp_mkQ (K₁ K : Submodule ℂ V) (q : (V ⧸ K₁) →ₗ[ℂ] X) (e : LinearMap.ker q = K.map K₁.mkQ)
    (hle : K₁ ≤ K) : LinearMap.ker (q ∘ₗ K₁.mkQ) = K := by
  rw [LinearMap.ker_comp, e, Submodule.comap_map_eq, Submodule.ker_mkQ, sup_eq_left.2 hle]

end Abstract

section Iter

variable (k : Type) [Field k]

noncomputable def embedding₂ (n : ℕ) : (j : ℕ) → GL (Fin n) k →* Mir k (n + j)
  | 0 => levi k n
  | j + 1 => ((levi k (n + j + 1)).comp (Mir k (n + j)).subtype).comp (embedding₂ n j)

end Iter

section IterRep

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem iterPhi_quotient (ψ : AddChar k Circle) (n : ℕ) : ∀ (j : ℕ) (τ : MRep k (n + j)),
    ∃ q : τ.V →ₗ[ℂ] TwJacquet (iterPhi k ψ j τ).ρ (MirUin k n) 1, Function.Surjective q ∧
      LinearMap.ker q = twKer τ.ρ (derUnipM k (n + j) n) (derCharM k ψ (n + j) n) ∧
      ∀ g v, q (τ.ρ (embedding₂ k n j g) v) = psiMinus k (iterPhi k ψ j τ).ρ g (q v) := by
  intro j
  induction j with
  | zero =>
    intro τ
    exact ⟨Submodule.mkQ _, Submodule.mkQ_surjective _,
      (Submodule.ker_mkQ _).trans (GlobalTheory.CompanionTheory.BZMir.twKer_MirUin_eq_derUnipM k ψ n τ.V τ.ρ), fun _ _ => rfl⟩
  | succ j ih =>
    intro τ
    obtain ⟨q', hs, hk, hi⟩ := ih (MRep.phiM k ψ τ)
    have hnm : n ≤ n + j := Nat.le_add_right n j
    let N₁ := MirUin k (n + j + 1)
    let θ₁ := mirChar k ψ (n + j)
    let N₂ := derUnipM k (n + j) n
    let θ₂ := derCharM k ψ (n + j) n
    let N := derUnipM k (n + j + 1) n
    let θ := derCharM k ψ (n + j + 1) n
    let s := (levi k (n + j + 1)).comp (Mir k (n + j)).subtype
    let K₁ := twKer τ.ρ N₁ θ₁
    let K := twKer τ.ρ N θ
    let L : Submodule ℂ (τ.V ⧸ K₁) :=
      twKer (twAct τ.ρ N₁ θ₁ s (levi_stab ψ (n + j))) N₂ θ₂
    have hle : K₁ ≤ K := by
      refine Submodule.span_le.2 ?_
      rintro w ⟨u, v, rfl⟩
      obtain ⟨hu, hθ⟩ := GlobalTheory.CompanionTheory.BZMirStep.MirUin_step ψ hnm u
      exact Submodule.subset_span ⟨⟨u, hu⟩, v, by rw [hθ]⟩
    have e : L = K.map K₁.mkQ := by
      apply le_antisymm
      · refine Submodule.span_le.2 ?_
        rintro w ⟨a, x, rfl⟩
        induction x using Submodule.Quotient.induction_on with
        | H v =>
          obtain ⟨ha, hθ⟩ := GlobalTheory.CompanionTheory.BZMirStep.levi_step ψ hnm a
          refine ⟨τ.ρ (s a) v - (θ ⟨s a, ha⟩ : ℂ) • v,
            Submodule.subset_span ⟨⟨s a, ha⟩, v, rfl⟩, ?_⟩
          change K₁.mkQ (τ.ρ (s a) v - (θ ⟨s a, ha⟩ : ℂ) • v) =
            K₁.mkQ (τ.ρ (s a) v) - (θ₂ a : ℂ) • K₁.mkQ v
          rw [map_sub, map_smul, hθ]
      · rw [Submodule.map_le_iff_le_comap]
        refine Submodule.span_le.2 ?_
        rintro w ⟨u, v, rfl⟩
        obtain ⟨u₁, a, hu⟩ := GlobalTheory.CompanionTheory.BZMirStep.derUnipM_decomp hnm u
        obtain ⟨hu₁, hθ₁⟩ := GlobalTheory.CompanionTheory.BZMirStep.MirUin_step ψ hnm u₁
        obtain ⟨ha, hθ₂⟩ := GlobalTheory.CompanionTheory.BZMirStep.levi_step ψ hnm a
        have hθ : θ u = θ₁ u₁ * θ₂ a := by
          have hu' : u = ⟨u₁, hu₁⟩ * ⟨s a, ha⟩ := Subtype.ext hu
          rw [hu', map_mul, hθ₁, hθ₂]
        have hdec : τ.ρ (u : Mir k (n + j + 1)) v - (θ u : ℂ) • v =
            (τ.ρ u₁ (τ.ρ (s a) v) - (θ₁ u₁ : ℂ) • τ.ρ (s a) v) +
              (θ₁ u₁ : ℂ) • (τ.ρ (s a) v - (θ₂ a : ℂ) • v) := by
          rw [hθ, hu, map_mul, mul_apply_eq_comp, Units.val_mul, smul_sub, mul_smul]
          abel
        have hz : τ.ρ u₁ (τ.ρ (s a) v) - (θ₁ u₁ : ℂ) • τ.ρ (s a) v ∈ K₁ :=
          Submodule.subset_span ⟨u₁, _, rfl⟩
        have hzero : K₁.mkQ (τ.ρ u₁ (τ.ρ (s a) v) - (θ₁ u₁ : ℂ) • τ.ρ (s a) v) = 0 :=
          (Submodule.Quotient.mk_eq_zero K₁).2 hz
        change K₁.mkQ _ ∈ L
        rw [hdec, map_add, hzero, zero_add, map_smul]
        refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, K₁.mkQ v, ?_⟩)
        change K₁.mkQ (τ.ρ (s a) v - (θ₂ a : ℂ) • v) =
          K₁.mkQ (τ.ρ (s a) v) - (θ₂ a : ℂ) • K₁.mkQ v
        rw [map_sub, map_smul]
    refine ⟨q' ∘ₗ K₁.mkQ, hs.comp K₁.mkQ_surjective, ?_, fun g v => ?_⟩
    · exact ker_comp_mkQ K₁ K q' (hk.trans e) hle
    · exact hi g (K₁.mkQ v)

end IterRep

section Concrete

variable {k : Type} [Field k]

theorem emb_inl_inl {n t N : ℕ} (h : n + t = N) (g : GL (Fin n) k × GL (Fin t) k) (i j : Fin n) :
    (emb₂ k (stdSum h) g : Matrix (Fin N) (Fin N) k) (stdSum h (Sum.inl i)) (stdSum h (Sum.inl j)) =
      (g.1 : Matrix (Fin n) (Fin n) k) i j := by
  rw [val_emb₂]
  simp [reindex_apply, submatrix_apply]

theorem emb_inl_inr {n t N : ℕ} (h : n + t = N) (g : GL (Fin n) k × GL (Fin t) k) (i : Fin n) (j : Fin t) :
    (emb₂ k (stdSum h) g : Matrix (Fin N) (Fin N) k) (stdSum h (Sum.inl i)) (stdSum h (Sum.inr j)) = 0 := by
  rw [val_emb₂]
  simp [reindex_apply, submatrix_apply]

theorem emb_inr_inl {n t N : ℕ} (h : n + t = N) (g : GL (Fin n) k × GL (Fin t) k) (i : Fin t) (j : Fin n) :
    (emb₂ k (stdSum h) g : Matrix (Fin N) (Fin N) k) (stdSum h (Sum.inr i)) (stdSum h (Sum.inl j)) = 0 := by
  rw [val_emb₂]
  simp [reindex_apply, submatrix_apply]

theorem emb_inr_inr {n t N : ℕ} (h : n + t = N) (g : GL (Fin n) k × GL (Fin t) k) (i j : Fin t) :
    (emb₂ k (stdSum h) g : Matrix (Fin N) (Fin N) k) (stdSum h (Sum.inr i)) (stdSum h (Sum.inr j)) =
      (g.2 : Matrix (Fin t) (Fin t) k) i j := by
  rw [val_emb₂]
  simp [reindex_apply, submatrix_apply]

theorem one_inr_inr {n t N : ℕ} (h : n + t = N) (i j : Fin t) :
    (1 : Matrix (Fin N) (Fin N) k) (stdSum h (Sum.inr i)) (stdSum h (Sum.inr j)) =
      (1 : Matrix (Fin t) (Fin t) k) i j := by
  rw [Matrix.one_apply, Matrix.one_apply]
  simp only [Equiv.apply_eq_iff_eq, Sum.inr.injEq]

theorem one_inl_inr {n t N : ℕ} (h : n + t = N) (i : Fin n) (j : Fin t) :
    (1 : Matrix (Fin N) (Fin N) k) (stdSum h (Sum.inl i)) (stdSum h (Sum.inr j)) = 0 := by
  simp

theorem one_inr_inl {n t N : ℕ} (h : n + t = N) (i : Fin t) (j : Fin n) :
    (1 : Matrix (Fin N) (Fin N) k) (stdSum h (Sum.inr i)) (stdSum h (Sum.inl j)) = 0 := by
  simp

end Concrete

section ConcreteChar

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

end ConcreteChar

section Entries

variable {k : Type} [Field k]

theorem glEmbMat_block_apply {n m : ℕ} (hnm : n ≤ m) (g : Matrix (Fin n) (Fin n) k) (A : Matrix (Fin m) (Fin m) k)
    (hA : ∀ r s : Fin m, A r s = if h : (r : ℕ) < n ∧ (s : ℕ) < n then g ⟨r, h.1⟩ ⟨s, h.2⟩
      else (1 : Matrix (Fin m) (Fin m) k) r s) (r s : Fin (m + 1)) :
    glEmbMat k m A r s = if h : (r : ℕ) < n ∧ (s : ℕ) < n then g ⟨r, h.1⟩ ⟨s, h.2⟩
      else (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) r s := by
  induction r using Fin.lastCases with
  | last =>
    rw [dite_eq_right (fun h => by have := h.1; simp at this; omega)]
    induction s using Fin.lastCases with
    | last => rw [GlobalTheory.CompanionTheory.BZMirStep.glEmbMat_last_last, one_apply_eq]
    | cast s => rw [GlobalTheory.CompanionTheory.BZMirStep.glEmbMat_last_castSucc, one_apply_ne (Fin.castSucc_ne_last s).symm]
  | cast r =>
    induction s using Fin.lastCases with
    | last =>
      rw [dite_eq_right (fun h => by have := h.2; simp at this; omega), GlobalTheory.CompanionTheory.BZMirStep.glEmbMat_castSucc_last,
        one_apply_ne (Fin.castSucc_ne_last r)]
    | cast s =>
      rw [GlobalTheory.CompanionTheory.BZMirStep.glEmbMat_castSucc_castSucc, hA r s]
      by_cases h : (r : ℕ) < n ∧ (s : ℕ) < n
      · rw [dite_eq_left h, dite_eq_left (by simpa using h)]
        rfl
      · rw [dite_eq_right h, dite_eq_right (by simpa using h)]
        rw [Matrix.one_apply, Matrix.one_apply]
        simp only [Fin.castSucc_inj]

theorem iotaM_apply (n : ℕ) (g : GL (Fin n) k) : ∀ (j : ℕ) (r s : Fin (n + j + 1)),
    (((embedding₂ k n j g : Mir k (n + j)) : GL (Fin (n + j + 1)) k) : Matrix (Fin (n + j + 1)) (Fin (n + j + 1)) k) r s =
      if h : (r : ℕ) < n ∧ (s : ℕ) < n then (g : Matrix (Fin n) (Fin n) k) ⟨r, h.1⟩ ⟨s, h.2⟩
      else (1 : Matrix (Fin (n + j + 1)) (Fin (n + j + 1)) k) r s
  | 0, r, s => glEmbMat_block_apply le_rfl (g : Matrix (Fin n) (Fin n) k) (g : Matrix (Fin n) (Fin n) k)
      (fun r s => by rw [dite_eq_left ⟨r.2, s.2⟩]) r s
  | j + 1, r, s => glEmbMat_block_apply (by omega) (g : Matrix (Fin n) (Fin n) k) _ (iotaM_apply n g j) r s

theorem iotaM_eq_emb (n j : ℕ) (g : GL (Fin n) k) :
    ((embedding₂ k n j g : Mir k (n + j)) : GL (Fin (n + j + 1)) k) =
      emb₂ k (stdSum (rfl : n + (j + 1) = n + j + 1)) (g, 1) := by
  apply Units.ext
  ext r s
  rw [iotaM_apply]
  obtain ⟨x, rfl⟩ := (stdSum (rfl : n + (j + 1) = n + j + 1)).surjective r
  obtain ⟨y, rfl⟩ := (stdSum (rfl : n + (j + 1) = n + j + 1)).surjective s
  rcases x with x | x <;> rcases y with y | y
  · rw [emb_inl_inl, dite_eq_left (by simp)]
    congr 1
  · rw [emb_inl_inr, dite_eq_right (by simp), one_inl_inr]
  · rw [emb_inr_inl, dite_eq_right (by simp), one_inr_inl]
  · rw [emb_inr_inr, dite_eq_right (by simp), one_inr_inr]
    rfl

end Entries

end GlobalTheory.CompanionTheory.BZMirJac

end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CentralProducts.LeviScalars.EmbScalarMemLevi

section

@[expose] public section

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib

namespace PositivityTheory.RgUd.Prod.LF

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def bb (n N : ℕ) : Fin N → Bool := fun i => decide (n ≤ (i : ℕ))

theorem bb_eq_true {n N : ℕ} (i : Fin N) : bb n N i = true ↔ n ≤ (i : ℕ) := by
  simp [bb]

theorem bb_eq_false {n N : ℕ} (i : Fin N) : bb n N i = false ↔ (i : ℕ) < n := by
  simp [bb]


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem unip_entries {n N : ℕ} {g : GL (Fin N) k}
    (hg : g ∈ GroundTheory.Automorphic.Parabolic.unipotentRadical k N (bb n N)) (i j : Fin N)
    (hij : ¬ ((i : ℕ) < n ∧ n ≤ (j : ℕ))) :
    (g : Matrix (Fin N) (Fin N) k) i j = (1 : Matrix (Fin N) (Fin N) k) i j := by
  obtain ⟨hP, hD⟩ := GroundTheory.Automorphic.Parabolic.mem_unipotentRadical.1 hg
  by_cases he : bb n N i = bb n N j
  · exact hD i j he
  · have hji : (j : ℕ) < n ∧ n ≤ (i : ℕ) := by
      by_cases hi : n ≤ (i : ℕ)
      · refine ⟨?_, hi⟩
        by_contra hj
        exact he (((bb_eq_true i).2 hi).trans ((bb_eq_true j).2 (by omega)).symm)
      · exfalso
        by_cases hj : n ≤ (j : ℕ)
        · exact hij ⟨by omega, hj⟩
        · exact he (((bb_eq_false i).2 (by omega)).trans ((bb_eq_false j).2 (by omega)).symm)
    have hlt : bb n N j < bb n N i := by
      rw [(bb_eq_false j).2 hji.1, (bb_eq_true i).2 hji.2]
      decide
    have h0 : (g : Matrix (Fin N) (Fin N) k) i j = 0 := hP hlt
    rw [h0, one_apply_ne (fun e => by rw [e] at hji; omega)]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem unip_le_derUnip {n N : ℕ} :
    GroundTheory.Automorphic.Parabolic.unipotentRadical k N (bb n N) ≤ derUnip k N n := by
  intro g hg
  have hE := unip_entries hg
  refine Subgroup.mem_inf.2 ⟨(mem_unipB k).2 ⟨fun i j hji => ?_, fun i => ?_⟩,
    (GlobalTheory.CompanionTheory.BZMirStep.mem_colFix_iff _).2 fun i j hj => hE i j (by omega)⟩
  · have := Fin.lt_def.1 hji
    rw [hE i j (by omega), one_apply_ne (ne_of_gt hji)]
  · rw [hE i i (by omega), one_apply_eq]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem derChar_unip {n N : ℕ} (ψ : AddChar k Circle) (u : derUnip k N n)
    (hu : (u : GL (Fin N) k) ∈ GroundTheory.Automorphic.Parabolic.unipotentRadical k N (bb n N)) :
    derChar k ψ N n u = 1 := by
  have hE := unip_entries hu
  show Circle.toUnits _ = 1
  rw [Finset.sum_eq_zero, AddChar.map_zero_eq_one, map_one]
  intro p hp
  obtain ⟨h1, h2⟩ := (Finset.mem_filter.1 hp).2
  refine (hE p.1 p.2 (by omega)).trans (one_apply_ne fun e => ?_)
  rw [e] at h1
  omega

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem sub_mem_twKer {n N : ℕ} (ψ : AddChar k Circle) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) (u : GL (Fin N) k)
    (hu : u ∈ GroundTheory.Automorphic.Parabolic.unipotentRadical k N (bb n N)) (w : V) :
    π u w - w ∈ twKer π (derUnip k N n) (derChar k ψ N n) :=
  Submodule.subset_span ⟨⟨u, unip_le_derUnip hu⟩, w, by rw [derChar_unip ψ _ hu]; simp⟩

def dd (n N : ℕ) (x : kˣ) : Fin N → k := fun i => if (i : ℕ) < n then (x : k) else 1

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem emb_scalar {n t N : ℕ} (h : n + t = N) (x : kˣ) :
    ((emb₂ k (stdSum h) (GeneralLinearGroup.scalar (Fin n) x, 1) : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) =
      diagonal (dd n N x) := by
  ext i j
  obtain ⟨a, rfl⟩ := (stdSum h).surjective i
  obtain ⟨b, rfl⟩ := (stdSum h).surjective j
  rcases a with a | a <;> rcases b with b | b
  · rw [GlobalTheory.CompanionTheory.BZMirJac.emb_inl_inl]
    by_cases hab : a = b
    · subst hab
      simp [dd, GeneralLinearGroup.scalar]
    · rw [diagonal_apply_ne _ (fun e => hab (Sum.inl_injective ((stdSum h).injective e)))]
      simp [GeneralLinearGroup.scalar, hab]
  · rw [GlobalTheory.CompanionTheory.BZMirJac.emb_inl_inr,
      diagonal_apply_ne _ (fun e => Sum.inl_ne_inr ((stdSum h).injective e))]
  · rw [GlobalTheory.CompanionTheory.BZMirJac.emb_inr_inl,
      diagonal_apply_ne _ (fun e => Sum.inr_ne_inl ((stdSum h).injective e))]
  · rw [GlobalTheory.CompanionTheory.BZMirJac.emb_inr_inr]
    by_cases hab : a = b
    · subst hab
      simp [dd]
    · rw [diagonal_apply_ne _ (fun e => hab (Sum.inr_injective ((stdSum h).injective e)))]
      simp [hab]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem emb_scalar_mem_levi {n t N : ℕ} (h : n + t = N) (x : kˣ) :
    emb₂ k (stdSum h) (GeneralLinearGroup.scalar (Fin n) x, 1) ∈ GroundTheory.Automorphic.Parabolic.levi k N (bb n N) := by
  rw [GroundTheory.Automorphic.Parabolic.mem_levi]
  intro i j hij
  have hne : i ≠ j := fun e => hij (e ▸ rfl)
  show ((emb₂ k (stdSum h) (GeneralLinearGroup.scalar (Fin n) x, 1) : GL (Fin N) k) :
    Matrix (Fin N) (Fin N) k) i j = 0
  rw [emb_scalar, diagonal_apply_ne _ hne]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem emb_scalar_comm {n t N : ℕ} (h : n + t = N) (x : kˣ) (y : GL (Fin N) k)
    (hy : y ∈ GroundTheory.Automorphic.Parabolic.levi k N (bb n N)) :
    emb₂ k (stdSum h) (GeneralLinearGroup.scalar (Fin n) x, 1) * y =
      y * emb₂ k (stdSum h) (GeneralLinearGroup.scalar (Fin n) x, 1) := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, emb_scalar]
  ext i j
  rw [diagonal_mul, mul_diagonal]
  by_cases he : bb n N i = bb n N j
  · have hd : dd n N x i = dd n N x j := by
      by_cases hi : (i : ℕ) < n
      · have hj : (j : ℕ) < n := (bb_eq_false j).1 (he.symm.trans ((bb_eq_false i).2 hi))
        simp [dd, hi, hj]
      · have hj : ¬ (j : ℕ) < n := fun hj =>
          hi ((bb_eq_false i).1 (he.trans ((bb_eq_false j).2 hj)))
        simp [dd, hi, hj]
    rw [hd, mul_comm]
  · have h0 : (y : Matrix (Fin N) (Fin N) k) i j = 0 := GroundTheory.Automorphic.Parabolic.mem_levi.1 hy i j he
    rw [h0, mul_zero, zero_mul]

theorem lfin_of_quot {n t N : ℕ} (h : n + t = N) (ψ : AddChar k Circle) {V X : Type} [AddCommGroup V]
    [Module ℂ V] [AddCommGroup X] [Module ℂ X] (π : Representation ℂ (GL (Fin N) k) V)
    (hπ : GlobalTheory.PRep.IsAdmissible π) (ρ : Representation ℂ (GL (Fin n) k) X) (p : V →ₗ[ℂ] X)
    (hp : Function.Surjective p) (hk : twKer π (derUnip k N n) (derChar k ψ N n) ≤ LinearMap.ker p)
    (hi : ∀ g v, p (π (emb₂ k (stdSum h) (g, 1)) v) = ρ g (p v)) (a : X) :
    ∃ U : Submodule ℂ X, FiniteDimensional ℂ U ∧ a ∈ U ∧
      ∀ (x : kˣ), ∀ u ∈ U, ρ (GeneralLinearGroup.scalar (Fin n) x) u ∈ U := by
  obtain ⟨v, rfl⟩ := hp a
  have hF : GroundTheory.Automorphic.IsAdmissible π := (PositivityTheory.rg.gu.whit.isAdmissible_iff π).1 hπ
  have hA := GroundTheory.Automorphic.Parabolic.isAdmissible_jacquetRep (β := bb n N) hF
  let J := GroundTheory.Automorphic.Parabolic.jacquetAction k N (bb n N) π
  have hpu : ∀ u : GroundTheory.Automorphic.Parabolic.unipotentRadical k N (bb n N),
      p ∘ₗ (π.comp (GroundTheory.Automorphic.Parabolic.unipotentRadical k N (bb n N)).subtype) u = p := by
    intro u
    refine LinearMap.ext fun w => ?_
    show p (π u w) = p w
    rw [← sub_eq_zero, ← map_sub]
    exact hk (sub_mem_twKer ψ π u u.2 w)
  let pb : GroundTheory.Automorphic.Parabolic.JacquetModule k N (bb n N) π →ₗ[ℂ] X :=
    Representation.Coinvariants.lift _ p hpu
  have hpb : ∀ w, pb (Representation.Coinvariants.mk _ w) = p w := fun w =>
    Representation.Coinvariants.lift_mk _ p hpu w
  let w₀ : GroundTheory.Automorphic.Parabolic.JacquetModule k N (bb n N) π := Representation.Coinvariants.mk _ v
  let KM : ℕ → Subgroup (GroundTheory.Automorphic.Parabolic.levi k N (bb n N)) := fun m =>
    (GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m).subgroupOf (GroundTheory.Automorphic.Parabolic.levi k N (bb n N))
  obtain ⟨m, hm⟩ := GroundTheory.Automorphic.Parabolic.exists_subgroupOf_congruenceSubgroup_subset (F := k) (n := N)
    (β := bb n N) ((hA.1 w₀).mem_nhds (one_mem (GroundTheory.Automorphic.stabilizerOf _ w₀)))
  have hfix : w₀ ∈ GroundTheory.Automorphic.fixedVectors J (KM m) := by
    have : w₀ ∈ GroundTheory.Automorphic.fixedVectors (GroundTheory.Automorphic.Parabolic.jacquetRep k N (bb n N) π) (KM m) :=
      fun x hx => hm hx
    rwa [GroundTheory.Automorphic.Parabolic.fixedVectors_jacquetRep_congruenceSubgroup] at this
  have hfin : FiniteDimensional ℂ (GroundTheory.Automorphic.fixedVectors J (KM m)) := by
    have := hA.2 (KM m)
      (GroundTheory.Automorphic.Parabolic.isCompact_subgroupOf_levi
        (GroundTheory.Automorphic.GLnLocal.isCompact_congruenceSubgroup k N m))
      (GroundTheory.Automorphic.Parabolic.isOpen_subgroupOf_levi
        (GroundTheory.Automorphic.GLnLocal.isOpen_congruenceSubgroup k N m))
    rwa [GroundTheory.Automorphic.Parabolic.fixedVectors_jacquetRep_congruenceSubgroup] at this
  refine ⟨(GroundTheory.Automorphic.fixedVectors J (KM m)).map pb, inferInstance, ⟨w₀, hfix, hpb v⟩, ?_⟩
  rintro x _ ⟨y, hy, rfl⟩
  obtain ⟨w, rfl⟩ := Representation.Coinvariants.mk_surjective _ y
  let z : GroundTheory.Automorphic.Parabolic.levi k N (bb n N) :=
    ⟨_, emb_scalar_mem_levi h x⟩
  refine ⟨J z (Representation.Coinvariants.mk _ w), ?_, ?_⟩
  · intro g hg
    have hc : g * z = z * g := Subtype.ext (emb_scalar_comm h x g g.2).symm
    show J g (J z _) = J z _
    rw [← Module.End.mul_apply, ← map_mul, hc, map_mul, Module.End.mul_apply]
    exact congrArg _ (hy g hg)
  · show pb (Representation.Coinvariants.mk _ (π _ w)) = _
    rw [hpb, hpb, hi]

theorem lfin_self {n : ℕ} (A : GRep k n) (hA : GlobalTheory.PRep.IsAdmissible A.ρ) : LFin A := by
  intro v
  have hF : GroundTheory.Automorphic.IsAdmissible A.ρ := (PositivityTheory.rg.gu.whit.isAdmissible_iff A.ρ).1 hA
  have hO : {g : GL (Fin n) k | A.ρ g v = v} ∈ nhds (1 : GL (Fin n) k) :=
    (hA.1 v).mem_nhds (by simp)
  obtain ⟨m, -, hm⟩ := (GroundTheory.Automorphic.GLnLocal.hasBasis_nhds_one k n).mem_iff.1 hO
  let K := GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k n m
  have hfin : FiniteDimensional ℂ (GroundTheory.Automorphic.fixedVectors A.ρ K) :=
    hF.2 K (GroundTheory.Automorphic.GLnLocal.isCompact_congruenceSubgroup k n m)
      (GroundTheory.Automorphic.GLnLocal.isOpen_congruenceSubgroup k n m)
  refine ⟨GroundTheory.Automorphic.fixedVectors A.ρ K, hfin, fun g hg => hm hg, ?_⟩
  intro x u hu g hg
  have hc : g * sc n x = sc n x * g := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul]
    show (g : Matrix (Fin n) (Fin n) k) * scalar (Fin n) (x : k) = scalar (Fin n) (x : k) * g
    exact ((scalar_commute (x : k) (fun r => Commute.all _ r) (g : Matrix (Fin n) (Fin n) k))).symm.eq
  show A.ρ g (A.ρ (sc n x) u) = A.ρ (sc n x) u
  rw [← Module.End.mul_apply, ← map_mul, hc, map_mul, Module.End.mul_apply, hu g hg]

variable (k)

theorem lfDeriv : LFDeriv k := by
  intro ψ _ n j π _ hA
  cases j with
  | zero => exact lfin_self π hA
  | succ j =>
    intro a
    obtain ⟨p, hp, hpk, hpi⟩ := GlobalTheory.CompanionTheory.BZMirJac.iterPhi_quotient ψ n j (resM k π.ρ)
    refine lfin_of_quot (rfl : n + (j + 1) = n + j + 1) ψ π.ρ hA (deriv k ψ j π.ρ) p hp ?_ ?_ a
    · intro w hw
      have hw' : w ∈ LinearMap.ker p := by
        rw [hpk, GlobalTheory.CompanionTheory.BZMirDer.twKer_resM_derUnipM]
        exact hw
      exact hw'
    · intro g v
      rw [← GlobalTheory.CompanionTheory.BZMirJac.iotaM_eq_emb]
      exact hpi g v

end PositivityTheory.RgUd.Prod.LF
end
end
end
