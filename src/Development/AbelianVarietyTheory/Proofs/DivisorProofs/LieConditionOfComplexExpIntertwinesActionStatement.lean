module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Uniformised
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Matrix.Trace
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.LinearAlgebra.Trace
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadTie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTangentCoordsBaseChangeSmoothCommGroupStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieMultIffFinrankCommonEigenspaceCoords
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieRepresentationSpectralProjectorsStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValSpMapComp

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeSpecDecomp

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

noncomputable section
namespace GlobalTheory.SpecBC

theorem baseChange_specDecomp : ∀ (g a m : ℕ) (O : Type) [CommRing O] (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (χ : Fin a → (O →+* ℂ)) (ω : O) (l l' : ℂ) (E : Fin a → Matrix (Fin g) (Fin g) ℂ), l ≠ l' → (∀ i j, i ≠ j → ∃ c, χ i c ≠ χ j c) → (∀ i, E i * E i = E i) → (∀ i, (E i).trace = (m : ℂ)) → (∀ i c, ρ c * E i = χ i c • E i) → (∀ i c, E i * ρ c = χ i c • E i) → (l - l') • ∑ i, E i = ρ ω - l' • (1 : Matrix (Fin g) (Fin g) ℂ) → (∀ (R' : Type) [CommRing R'] (j : ℂ →+* R') (x : Fin g → R'), (ρ ω).map j *ᵥ x = j l • x → ∃ y : Fin a → Fin g → R', (∀ i c, (ρ c).map j *ᵥ y i = j (χ i c) • y i) ∧ x = ∑ i, y i) ∧ ∀ (k : Type) [Field k] (j : ℂ →+* k) (i : Fin a), χ i ω = l → Module.finrank k (⨅ c, LinearMap.ker (Matrix.mulVecLin ((ρ c).map j) - j (χ i c) • LinearMap.id) : Submodule k (Fin g → k)) = m := by
  intro g a m O _ ρ χ ω l l' E hll hsep hidem htr hrE hEr hsum
  have hsm : ∀ (R' : Type) [CommRing R'] (j : ℂ →+* R') (r : ℂ) (M : Matrix (Fin g) (Fin g) ℂ),
      (r • M).map j = j r • M.map j := by
    intro R' _ j r M; ext; simp
  have hmul : ∀ (R' : Type) [CommRing R'] (j : ℂ →+* R') (M N : Matrix (Fin g) (Fin g) ℂ),
      (M * N).map j = M.map j * N.map j := by
    intro R' _ j M N; exact Matrix.map_mul

  have hrel : ∀ (R' : Type) [CommRing R'] (j : ℂ →+* R') (x : Fin g → R'),
      j (l - l') • ∑ i, (E i).map j *ᵥ x = (ρ ω).map j *ᵥ x - j l' • x := by
    intro R' _ j x
    have h := congrArg (fun M => (RingHom.mapMatrix j M) *ᵥ x) hsum
    simp only [RingHom.mapMatrix_apply] at h
    have hs : (∑ i, E i).map j = ∑ i, (E i).map j := by ext; simp [Matrix.sum_apply]
    rw [hsm, hs, Matrix.smul_mulVec, Matrix.sum_mulVec] at h
    rw [h, Matrix.map_sub _ (map_sub j), Matrix.sub_mulVec, hsm, Matrix.smul_mulVec, Matrix.map_one _ (map_zero j) (map_one j),
      Matrix.one_mulVec]
  refine ⟨fun R' _ j x hx => ?_, fun k _ j i hi => ?_⟩
  · refine ⟨fun i => (E i).map j *ᵥ x, fun i c => ?_, ?_⟩
    · rw [Matrix.mulVec_mulVec, ← hmul, hrE, hsm, Matrix.smul_mulVec]
    · have hu : IsUnit (j (l - l')) := (sub_ne_zero.mpr hll).isUnit.map j
      have h := hrel R' j x
      rw [hx, ← sub_smul, ← map_sub] at h
      exact (hu.smul_left_cancel.mp h).symm
  · have hj : ∀ z : ℂ, z ≠ 0 → j z ≠ 0 := fun z hz => (hz.isUnit.map j).ne_zero
    have hK : (⨅ c, LinearMap.ker (Matrix.mulVecLin ((ρ c).map j) - j (χ i c) • LinearMap.id) :
        Submodule k (Fin g → k)) = LinearMap.range (Matrix.mulVecLin ((E i).map j)) := by
      ext y
      simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, Matrix.mulVecLin_apply,
        LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero, LinearMap.mem_range]
      constructor
      · intro hy
        refine ⟨y, ?_⟩
        have hz : ∀ i', i' ≠ i → (E i').map j *ᵥ y = 0 := by
          intro i' hne
          obtain ⟨c, hc⟩ := hsep i' i hne
          have h1 : (E i').map j *ᵥ ((ρ c).map j *ᵥ y) = j (χ i' c) • ((E i').map j *ᵥ y) := by
            rw [Matrix.mulVec_mulVec, ← hmul, hEr, hsm, Matrix.smul_mulVec]
          rw [hy c, Matrix.mulVec_smul] at h1
          have h2 : (j (χ i' c) - j (χ i c)) • ((E i').map j *ᵥ y) = 0 := by
            rw [sub_smul, ← h1, sub_self]
          rw [← map_sub] at h2
          exact (smul_eq_zero.mp h2).resolve_left (hj _ (sub_ne_zero.mpr hc))
        have h := hrel k j y
        rw [hy ω, hi, ← sub_smul, ← map_sub,
          Finset.sum_eq_single i (fun b _ hb => hz b hb) (by simp)] at h
        exact smul_right_injective _ (hj _ (sub_ne_zero.mpr hll)) h
      · rintro ⟨z, rfl⟩ c
        rw [Matrix.mulVec_mulVec, ← hmul, hrE, hsm, Matrix.smul_mulVec]
    rw [hK]
    have hPP : (E i).map j * (E i).map j = (E i).map j := by rw [← hmul, hidem]
    have he : IsIdempotentElem (Matrix.mulVecLin ((E i).map j)) := by
      unfold IsIdempotentElem
      rw [Module.End.mul_eq_comp, ← Matrix.mulVecLin_mul, hPP]
    have h1 := (LinearMap.IsIdempotentElem.isProj_range _ he).trace
    rw [← Matrix.toLin'_apply', LinearMap.trace_eq_matrix_trace k (Pi.basisFun k (Fin g)),
      LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin'] at h1
    have htj : ((E i).map j).trace = j (E i).trace := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp [Matrix.trace, map_sum]
    rw [htj, htr, map_natCast] at h1
    haveI : CharZero k := (RingHom.charZero_iff j.injective).1 inferInstance
    exact_mod_cast h1.symm

end GlobalTheory.SpecBC
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TanScalDecomp

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

noncomputable section

namespace GlobalTheory.LieCoordMult

theorem tanScal_decomp : ∀ (O : Type) [Ring O] (F' : Type) (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (act : OActN O G) (R' : Type) [CommRing R'] (x : Sp R' ⟶ S) (n a : ℕ) (T : (Fin n → R') → (epsPtR x ⟶ G)) (A : O → Matrix (Fin n) (Fin n) R') (emb : F' → O) (ω : F') (l : R') (χ : Fin a → F' → R'), Function.Injective T → (∀ v : epsPtR x ⟶ G, spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ v.left = (1 : Over.mk x ⟶ G).left ↔ v ∈ Set.range T) → (∀ c c', T (c + c') = T c * T c') → (∀ (s : R') c, (T (s • c)).left = spMap (epsScaleR s) ≫ (T c).left) → (∀ b c, T c ≫ act.act b = T (A b *ᵥ c)) → (∀ y : Fin n → R', A (emb ω) *ᵥ y = l • y → ∃ z : Fin a → Fin n → R', (∀ i c, A (emb c) *ᵥ z i = χ i c • z i) ∧ y = ∑ i, z i) → ∀ v : epsPtR x ⟶ G, IsTanScal act x (emb ω) l v → ∃ w : Fin a → (epsPtR x ⟶ G), (∀ i c, IsTanScal act x (emb c) (χ i c) (w i)) ∧ v = (List.ofFn w).prod := by
  intro O _ F' S G _ _ act R' _ x n a T A emb ω l χ hinj htan hadd hsc hact hdec v hv
  have T0 : T 0 = 1 := by
    have h := hadd 0 0
    rw [add_zero] at h
    exact mul_eq_left.mp h.symm
  have Tsum : ∀ (m : ℕ) (y : Fin m → (Fin n → R')), (List.ofFn (fun i => T (y i))).prod = T (∑ i, y i) := by
    intro m
    induction m with
    | zero => intro y; simp [T0]
    | succ m ih => intro y; rw [List.ofFn_succ, List.prod_cons, ih, Fin.sum_univ_succ, hadd]
  have eig : ∀ (b : O) (c : R') (w : epsPtR x ⟶ G), IsTanScal act x b c w ↔ ∃ y, A b *ᵥ y = c • y ∧ w = T y := by
    intro b c w
    constructor
    · rintro ⟨h1, h2⟩
      obtain ⟨y, rfl⟩ := (htan w).1 h1
      refine ⟨y, hinj (Over.OverMorphism.ext ?_), rfl⟩
      rw [← hact, h2, hsc]
    · rintro ⟨y, hy, rfl⟩
      refine ⟨(htan _).2 ⟨y, rfl⟩, ?_⟩
      rw [hact, hy, hsc]
  obtain ⟨y, hy, rfl⟩ := (eig _ _ _).1 hv
  obtain ⟨z, hz, rfl⟩ := hdec y hy
  exact ⟨fun i => T (z i), fun i c => (eig _ _ _).2 ⟨z i, hz i c, rfl⟩, (Tsum a z).symm⟩

end GlobalTheory.LieCoordMult
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieConditionOfComplexExpIntertwinesAction

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

theorem GlobalTheory.UPel.HT.lie_of_complexExp : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (σ : R →+* ℂ) (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (act : OActN D.O A) (e : (Fin D.g → ℂ) → (Over.mk (𝟙 (Sp ℂ)) ⟶ A)), IsAbelianScheme A → SmoothOfRelativeDimension D.g A.hom → IsExp (𝟙 (Sp ℂ)) e → (∀ a z, e (ρ a *ᵥ z) = e z ≫ act.act a) → b.IsType σ ρ → (∀ (R' : Type) [CommRing R'] (β : R →+* R') (x : Sp R' ⟶ Sp ℂ), x ≫ spMap σ = spMap β → ∀ v : epsPtR x ⟶ A, IsTanScal act x (algebraMap (𝓞 D.F) D.O D.ω) (β b.ρ) v → ∃ w : Fin D.a → (epsPtR x ⟶ A), (∀ i, ∀ c : 𝓞 D.F, IsTanScal act x (algebraMap (𝓞 D.F) D.O c) (β (b.t i c)) (w i)) ∧ v = (List.ofFn w).prod) ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Sp ℂ) (β : R →+* k), x ≫ spMap σ = spMap β → ∀ i, LieMult (act.toF D) x (β.comp (b.t i)) D.m := by
  intro p _ D R _ b N σ ρ A _ _ act e hab hsm hexp hlin hty
  have hsmooth : Smooth A.hom := SmoothOfRelativeDimension.smooth D.g A.hom
  obtain ⟨n, M, hT⟩ := GlobalTheory.T.exists_tangent_coords_base_change_smooth_comm_group ℂ A hsmooth
  obtain ⟨T0, h0inj, h0tan, h0add, h0sc, h0act⟩ := hT ℂ (RingHom.id ℂ)
  have hid : spMap (RingHom.id ℂ) = 𝟙 (Sp ℂ) := by simp [spMap]
  obtain ⟨L, hL⟩ := GlobalTheory.ExpCoord.expCoord D.g n A e (spMap (RingHom.id ℂ)) T0 hid hexp h0inj h0tan h0add h0sc
  have hLρ : ∀ (a : D.O) w, L (ρ a *ᵥ w) = M (act.act a) *ᵥ L w := fun a w => by
    have := hL (act.act a) (act.hom a) ((M (act.act a)).map (RingHom.id ℂ)) (ρ a)
      (fun c => h0act _ (act.hom a) c) (hlin a) w
    simpa using this
  have hn : n = D.g := by simpa using L.finrank_eq.symm
  subst hn
  set P : Matrix (Fin D.g) (Fin D.g) ℂ := LinearMap.toMatrix' L.toLinearMap with hP
  have hPv : ∀ w, P *ᵥ w = L w := fun w => LinearMap.toMatrix'_mulVec _ w
  have hMP : ∀ a, M (act.act a) * P = P * ρ a := fun a => by
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun w => ?_
    simp only [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, hPv]
    exact (hLρ a w).symm
  have hPdet : IsUnit P.det := by
    rw [hP, LinearMap.det_toMatrix']
    exact LinearEquiv.isUnit_det' L
  have key : ∀ (R' : Type) [CommRing R'] (j : ℂ →+* R'), ∃ T' : (Fin D.g → R') → (epsPtR (spMap j) ⟶ A),
      Function.Injective T' ∧
      (∀ v : epsPtR (spMap j) ⟶ A, spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ v.left =
        (1 : Over.mk (spMap j) ⟶ A).left ↔ v ∈ Set.range T') ∧
      (∀ c c', T' (c + c') = T' c * T' c') ∧
      (∀ (s : R') c, (T' (s • c)).left = spMap (epsScaleR s) ≫ (T' c).left) ∧
      ∀ (a : D.O) c, T' c ≫ act.act a = T' ((ρ a).map j *ᵥ c) := by
    intro R' _ j
    obtain ⟨T, hinj, htan, hadd, hsc, hact⟩ := hT R' j
    have hu : IsUnit (P.map j) := by
      rw [Matrix.isUnit_iff_isUnit_det]
      have : (P.map j).det = j P.det := by rw [RingHom.map_det]; rfl
      rw [this]
      exact hPdet.map j
    have hinv : (P.map j)⁻¹ * P.map j = 1 := Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hu)
    have hPinj : Function.Injective (P.map j).mulVec := fun c c' h => by
      have := congrArg ((P.map j)⁻¹ *ᵥ ·) h
      simpa [Matrix.mulVec_mulVec, hinv] using this
    have hPsurj : Function.Surjective (P.map j).mulVec := Matrix.mulVec_surjective_iff_isUnit.2 hu
    refine ⟨fun c => T (P.map j *ᵥ c), hinj.comp hPinj, fun v => ?_, fun c c' => ?_, fun s c => ?_, fun a c => ?_⟩
    · rw [htan v]
      constructor
      · rintro ⟨y, rfl⟩
        obtain ⟨c, rfl⟩ := hPsurj y
        exact ⟨c, rfl⟩
      · rintro ⟨c, rfl⟩
        exact ⟨_, rfl⟩
    · simp only [Matrix.mulVec_add, hadd]
    · simp only [Matrix.mulVec_smul, hsc]
    · simp only
      rw [hact _ (act.hom a), Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.map_mul, ← Matrix.map_mul, hMP]
  obtain ⟨E, hE1, hE2, hE3, hE4, hE5⟩ := GlobalTheory.T.lie_representation_spectral_projectors p D R b σ ρ hty
  have hroot : σ b.ρ ^ 2 - D.tr * σ b.ρ + D.nm = 0 := by
    have := congrArg σ b.ρ_root
    simpa using this
  have hne : σ b.ρ ≠ (D.tr : ℂ) - σ b.ρ := by
    intro h
    have h2 : (((D.tr ^ 2 - 4 * D.nm : ℤ)) : ℂ) = 0 := by
      push_cast
      linear_combination (2 * σ b.ρ - D.tr) * h - 4 * hroot
    have := D.disc_neg
    rw [Int.cast_eq_zero] at h2
    omega
  have hdist : ∀ i j, i ≠ j → ∃ c, (σ.comp (b.t i)) c ≠ (σ.comp (b.t j)) c := by
    intro i j hij
    by_contra hc
    push Not at hc
    have hle : Ideal.span (Set.range fun x => b.t i x - b.t j x) ≤ RingHom.ker σ := by
      rw [Ideal.span_le]
      rintro _ ⟨x, rfl⟩
      simp only [SetLike.mem_coe, RingHom.mem_ker, map_sub]
      exact sub_eq_zero.2 (hc x)
    rw [b.comax i j hij, top_le_iff] at hle
    have h1 : (1 : R) ∈ RingHom.ker σ := hle ▸ Submodule.mem_top
    simp at h1
  have hE5' : (σ b.ρ - ((D.tr : ℂ) - σ b.ρ)) • ∑ i, E i =
      (ρ.comp (algebraMap (𝓞 D.F) D.O)) D.ω - ((D.tr : ℂ) - σ b.ρ) • (1 : Matrix (Fin D.g) (Fin D.g) ℂ) := by
    rw [show σ b.ρ - ((D.tr : ℂ) - σ b.ρ) = 2 * σ b.ρ - D.tr by ring]
    exact hE5
  have hbc := GlobalTheory.SpecBC.baseChange_specDecomp D.g D.a D.m (𝓞 D.F) (ρ.comp (algebraMap (𝓞 D.F) D.O)) (fun i => σ.comp (b.t i)) D.ω
    (σ b.ρ) ((D.tr : ℂ) - σ b.ρ) E hne hdist hE1 hE2 hE3 hE4 hE5'
  have hpt : ∀ (R' : Type) [CommRing R'] (β : R →+* R') (x : Sp R' ⟶ Sp ℂ), x ≫ spMap σ = spMap β →
      ∃ j : ℂ →+* R', x = spMap j ∧ β = j.comp σ := by
    intro R' _ β x hx
    have hxj : x = spMap (Spec.preimage x).hom := by simp [spMap]
    generalize (Spec.preimage x).hom = j at hxj
    subst hxj
    refine ⟨j, rfl, ?_⟩
    have e1 : spMap (j.comp σ) = spMap j ≫ spMap σ := by
      simp [spMap, ← Spec.map_comp]
    rw [hx] at e1
    have := Spec.map_injective e1
    exact (congrArg CommRingCat.Hom.hom this).symm
  refine ⟨fun R' _ β x hx v hv => ?_, fun k _ _ x β hx i => ?_⟩
  · obtain ⟨j, rfl, rfl⟩ := hpt R' β x hx
    obtain ⟨T', h1, h2, h3, h4, h5⟩ := key R' j
    exact GlobalTheory.LieCoordMult.tanScal_decomp D.O (𝓞 D.F) (Sp ℂ) A act R' (spMap j) D.g D.a T' (fun a => (ρ a).map j)
      (algebraMap (𝓞 D.F) D.O) D.ω ((j.comp σ) b.ρ) (fun i c => (j.comp σ) (b.t i c)) h1 h2 h3 h4 h5
      (fun y hy => hbc.1 R' j y hy) v hv
  · obtain ⟨j, rfl, rfl⟩ := hpt k β x hx
    obtain ⟨T', h1, h2, h3, h4, h5⟩ := key k j
    exact (GlobalTheory.LieCoordMult.lieMult_iff_finrank_eig ℂ A (𝓞 D.F) (act.toF D) D.g k j T' (fun c => (ρ (algebraMap (𝓞 D.F) D.O c)).map j) h1 h2 h3 h4
      (fun a c => h5 _ c) ((j.comp σ).comp (b.t i)) D.m).2 (hbc.2 k j i (by simp only [RingHom.comp_apply, b.t_ω]))
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieConditionOfComplexExpIntertwinesActionStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

theorem _root_.GlobalTheory.T.lieCondition_of_complexExp_intertwines_action : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (σ : R →+* ℂ) (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (act : OActN D.O A) (e : (Fin D.g → ℂ) → (Over.mk (𝟙 (Sp ℂ)) ⟶ A)), IsAbelianScheme A → SmoothOfRelativeDimension D.g A.hom → IsExp (𝟙 (Sp ℂ)) e → (∀ a z, e (ρ a *ᵥ z) = e z ≫ act.act a) → b.IsType σ ρ → (∀ (R' : Type) [CommRing R'] (β : R →+* R') (x : Sp R' ⟶ Sp ℂ), x ≫ spMap σ = spMap β → ∀ v : epsPtR x ⟶ A, IsTanScal act x (algebraMap (𝓞 D.F) D.O D.ω) (β b.ρ) v → ∃ w : Fin D.a → (epsPtR x ⟶ A), (∀ i, ∀ c : 𝓞 D.F, IsTanScal act x (algebraMap (𝓞 D.F) D.O c) (β (b.t i c)) (w i)) ∧ v = (List.ofFn w).prod) ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Sp ℂ) (β : R →+* k), x ≫ spMap σ = spMap β → ∀ i, LieMult (act.toF D) x (β.comp (b.t i)) D.m := by
  first | exact @GlobalTheory.UPel.HT.lie_of_complexExp | exact GlobalTheory.UPel.HT.lie_of_complexExp | (intros; apply GlobalTheory.UPel.HT.lie_of_complexExp <;> assumption)
end
end
