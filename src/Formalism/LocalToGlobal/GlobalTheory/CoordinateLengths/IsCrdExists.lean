module

public import Formalism.LocalToGlobal.GlobalTheory.CoordinateLengths.PairingEqLimitPairing
import Formalism.LocalToGlobal.GlobalTheory.GL6.WeylLengthDiagonalUnitUniformiser
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
public import Mathlib.RingTheory.Length
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.TypeStar
public import Formalism.LocalToGlobal.GroupLattices.DownNaturalLevelZero
public import Formalism.LocalToGlobal.GlobalTheory.GL6.LatticeInclusionFamilyOf

-- Source module: Formalism.LocalToGlobal.GlobalTheory.CoordinateLengths.PairingAdjointness

section

@[expose] public section

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LemB

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms NumberField MvPolynomial Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

variable (D : D7)

def intSubm (w : D.what₂.places.Pl) {N : ℕ} (lam : D.what₂.Tau → DomWeight N) :
    Submodule (bwA_Ow D w) (MvPolynomial (D.what₂.Tau × Fin N × Fin N) ℂ) :=
  Submodule.span (bwA_Ow D w) (Formalism.L2.Forms.IntSpan D w lam : Set _)

theorem intSubm_eq (w : D.what₂.places.Pl) {N : ℕ} (lam : D.what₂.Tau → DomWeight N) (κ : D.what₂.Tau → Type)
    [∀ τ, Fintype (κ τ)] (b : ∀ τ, Module.Basis (κ τ) ℤ (delSq ℤ N (lam τ))) :
    intSubm D w lam = tenSpan κ (fun τ k => MvPolynomial.map (Int.castRingHom ℂ)
      ((b τ k : delSq ℤ N (lam τ)) : MvPolynomial (Fin N × Fin N) ℤ)) (bwA_Ow D w) := by
  classical
  unfold intSubm Formalism.L2.Forms.IntSpan tenSpan Formalism.L2.Forms.ten bwA_Ow
  apply le_antisymm
  · rw [Submodule.span_le]
    intro p hp
    rw [SetLike.mem_coe] at hp
    induction hp using AddSubgroup.closure_induction with
    | mem x hx =>
      obtain ⟨r, f, hr, hf, rfl⟩ := hx
      have hfe : ∀ τ, rename (Prod.mk τ) (map (Int.castRingHom ℂ) (f τ)) =
          ∑ k, (b τ).repr ⟨f τ, hf τ⟩ k • rename (Prod.mk τ) (map (Int.castRingHom ℂ)
            ((b τ k : delSq ℤ N (lam τ)) : MvPolynomial (Fin N × Fin N) ℤ)) := by
        intro τ
        have h2 := congrArg Subtype.val ((b τ).sum_repr ⟨f τ, hf τ⟩)
        rw [Submodule.coe_sum] at h2
        simp only [Submodule.coe_smul] at h2
        conv_lhs => rw [← h2]

        rw [map_sum, map_sum]
        simp only [map_zsmul]
      simp only [hfe]
      rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
      refine Submodule.smul_mem _ (⟨_, Subring.mem_map.2 ⟨r, hr, rfl⟩⟩ : ↥(Subring.map D.what₂.embLL (intW D.what₂.places w))) ?_
      refine Submodule.sum_mem _ fun g _ => ?_
      simp only [zsmul_eq_mul, Finset.prod_mul_distrib, ← Int.cast_prod]
      rw [← zsmul_eq_mul]
      apply zsmul_mem
      apply Submodule.subset_span
      exact ⟨g, rfl⟩
    | zero => exact Submodule.zero_mem _
    | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
    | neg x _ hx => exact Submodule.neg_mem _ hx
  · rw [Submodule.span_le]
    rintro _ ⟨g, rfl⟩
    apply Submodule.subset_span
    apply AddSubgroup.subset_closure
    refine ⟨1, fun τ => ((b τ (g τ) : delSq ℤ N (lam τ)) : MvPolynomial (Fin N × Fin N) ℤ), Subring.one_mem _,
      fun τ => (b τ (g τ)).2, ?_⟩
    rw [map_one, one_smul]

theorem bwA_span_basis (O : Subring ℂ) {N : ℕ} (ν : Fin N → ℕ) {κ : Type} [Fintype κ]
    (b : Module.Basis κ ℤ (Formalism.GradedWeylDivisibility.weyl ℤ N N le_rfl ν)) :
    bwA_span (K := ℂ) O le_rfl ν = Submodule.span O (Set.range fun k => MvPolynomial.map (Int.castRingHom ℂ)
      ((b k : Formalism.GradedWeylDivisibility.weyl ℤ N N le_rfl ν) : MvPolynomial (Fin N × Fin N) ℤ)) := by
  unfold bwA_span
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨p, hp, rfl⟩
    have h2 := congrArg Subtype.val (b.sum_repr ⟨p, hp⟩)
    rw [Submodule.coe_sum] at h2
    simp only [Submodule.coe_smul] at h2

    rw [← h2, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [map_zsmul]
    apply zsmul_mem
    apply Submodule.subset_span
    exact ⟨i, rfl⟩
  · rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    exact Submodule.subset_span (Set.mem_image_of_mem _ (b k).2)

variable (u : D.what₂.Word)

theorem cls_len_D (A : AtTTied u) (w : D.what₂.places.Pl) (hw : OverT D u w)
    (v : (D.mem u).A.vT) (Lv : LvTied u A 0 (Nat.zero_le _)) (c : (D.mem u).C.cls 0)
    (hLc0 : clsCrd D u 0 (Nat.zero_le _) c ≤ Ld D u 0 (Nat.zero_le _) c) (B B' : GL (Fin (D.R.N 0)) D.host.E)
    (hB : IsLocBasis (D.mem u).A.T (Ld D u 0 (Nat.zero_le _) c : Set _) B)
    (hB' : IsLocBasis (D.mem u).A.T (Lk A 0 (Nat.zero_le _) v c : Set _) B')
    (hunit : ((((B⁻¹ * B' : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E)).map
        (embT D ((D.fm u).tauOf w v))).det * (((D.mem u).A.T : ℂ))⁻¹ ∈ bwA_Ow D w ∧
      ((D.mem u).A.T : ℂ) * (((((B⁻¹ * B' : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E)).map
        (embT D ((D.fm u).tauOf w v))).det)⁻¹ ∈ bwA_Ow D w) :
    ∃ n : ℕ, Module.length (bwA_Ow D w)
      ((((intSubm D w ((D.fm u).lam 0)).map
            ((Formalism.L2.Forms.subP (bwA_N D ((D.fm u).tauOf w v) B B')).toLinearMap.restrictScalars (bwA_Ow D w))).map
          (scO (bwA_Ow D w) _ ((bwA_N D ((D.fm u).tauOf w v) B B' ((D.fm u).tauOf w v)).det ^
            ((D.fm u).lam 0 ((D.fm u).tauOf w v)).detShift))) ⧸
        ((intSubm D w ((D.fm u).lam 0)).map
            (scO (bwA_Ow D w) _ (((D.mem u).A.T : ℂ) ^ (D.fm u).bTop ((D.fm u).tauOf w v)))).comap
          (((intSubm D w ((D.fm u).lam 0)).map
            ((Formalism.L2.Forms.subP (bwA_N D ((D.fm u).tauOf w v) B B')).toLinearMap.restrictScalars (bwA_Ow D w))).map
          (scO (bwA_Ow D w) _ ((bwA_N D ((D.fm u).tauOf w v) B B' ((D.fm u).tauOf w v)).det ^
            ((D.fm u).lam 0 ((D.fm u).tauOf w v)).detShift))).subtype) = n ∧
      (D.R.k : ℚ) * n = (D.what₂.places.ramIdx w : ℚ) *
        ((∏ τ, Module.finrank ℤ (delSq ℤ (D.R.N 0) ((D.fm u).lam 0 τ)) : ℕ) : ℚ) *
        ((wsum ((D.fm u).lam 0 ((D.fm u).tauOf w v)) : ℚ) + (D.R.k : ℚ) * ((D.fm u).bTop ((D.fm u).tauOf w v) : ℚ)) := by
  classical
  choose κ hκ b0 _ _ _ _ using fun τ => weyl_homogeneous_basis (r := D.R.N 0) (n := D.R.N 0) le_rfl ((D.fm u).lam 0 τ).natW
    (dominant_natWeight_antitone ((D.fm u).lam 0 τ))
  let _ := hκ
  let b : ∀ τ, Module.Basis (κ τ) ℤ (delSq ℤ (D.R.N 0) ((D.fm u).lam 0 τ)) := b0
  obtain ⟨n, hn, hrel⟩ := length_factor_local_basis D u A w hw v Lv c hLc0 B B' hB hB' hunit _ rfl
  have hli : ∀ τ, τ ≠ (D.fm u).tauOf w v → LinearIndependent ℂ (fun k => MvPolynomial.map (Int.castRingHom ℂ)
      ((b τ k : delSq ℤ (D.R.N 0) ((D.fm u).lam 0 τ)) : MvPolynomial (Fin (D.R.N 0) × Fin (D.R.N 0)) ℤ)) := fun τ _ =>
    weyl_basis_lin_indep_field le_rfl ((D.fm u).lam 0 τ).natW (dominant_natWeight_antitone ((D.fm u).lam 0 τ)) ℂ (b0 τ)
  have ho : ∀ τ, τ ≠ (D.fm u).tauOf w v → bwA_N D ((D.fm u).tauOf w v) B B' τ = 1 := by
    intro τ h
    unfold bwA_N
    rw [ite_eq_right h]
  have hcard : ∀ τ, Module.finrank ℤ (delSq ℤ (D.R.N 0) ((D.fm u).lam 0 τ)) = Fintype.card (κ τ) := fun τ =>
    Module.finrank_eq_card_basis (b τ)
  refine ⟨(∏ τ : {τ // τ ≠ (D.fm u).tauOf w v}, Fintype.card (κ τ.1)) * n, ?_, ?_⟩
  · rw [intSubm_eq D w ((D.fm u).lam 0) κ b]
    refine (cls_len ((D.fm u).tauOf w v) κ _ (bwA_Ow D w) hli _
      (bwA_span_basis (bwA_Ow D w) ((D.fm u).lam 0 ((D.fm u).tauOf w v)).natW (b0 ((D.fm u).tauOf w v)))
      (bwA_N D ((D.fm u).tauOf w v) B B') ho _ _).trans ?_
    rw [hn]
    simp
  · have hprod : (∏ τ, Module.finrank ℤ (delSq ℤ (D.R.N 0) ((D.fm u).lam 0 τ))) =
        Module.finrank ℤ (delSq ℤ (D.R.N 0) ((D.fm u).lam 0 ((D.fm u).tauOf w v))) *
          ∏ τ : {τ // τ ≠ (D.fm u).tauOf w v}, Fintype.card (κ τ.1) := by
      simp only [hcard]
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ ((D.fm u).tauOf w v))]
      congr 1
      exact Finset.prod_subtype (Finset.univ.erase ((D.fm u).tauOf w v)) (p := fun τ => τ ≠ (D.fm u).tauOf w v)
        (fun x => by simp) (fun τ => Fintype.card (κ τ))
    rw [hprod]
    push_cast
    linear_combination (∏ τ : {τ // τ ≠ (D.fm u).tauOf w v}, (Fintype.card (κ τ.1) : ℚ)) * hrel

end Formalism.L2.GlobalTheoryTheory.LemB
end
end
end

-- Source module: Formalism.LocalToGlobal.GlobalTheory.CoordinateLengths.PairingContinuityBound

section

@[expose] public section

namespace Formalism.L2.GlobalTheoryTheory.LemB

theorem len_equiv_semilinear {R R' M M' : Type*} [Ring R] [Ring R'] [AddCommGroup M] [Module R M]
    [AddCommGroup M'] [Module R' M'] {σ : R →+* R'} {σ' : R' →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
    (e : M ≃ₛₗ[σ] M') : Module.length R M = Module.length R' M' := by
  let e' : Submodule R M ≃o Submodule R' M' := Submodule.orderIsoMapComap e
  unfold Module.length
  congr 1
  exact Order.krullDim_eq_of_orderIso e'

noncomputable def quotEquivSL {R R' M M' : Type*} [Ring R] [Ring R'] [AddCommGroup M] [Module R M]
    [AddCommGroup M'] [Module R' M'] {σ : R →+* R'} {σ' : R' →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
    (e : M ≃ₛₗ[σ] M') (P : Submodule R M) (Q : Submodule R' M') (h : P.map (e : M →ₛₗ[σ] M') = Q) :
    (M ⧸ P) ≃ₛₗ[σ] (M' ⧸ Q) :=
  LinearEquiv.ofLinearMap
    (P.mapQ Q (e : M →ₛₗ[σ] M') (by rw [← h]; exact Submodule.le_comap_map _ _))
    (Q.mapQ P (e.symm : M' →ₛₗ[σ'] M) (by
      rw [← h]; rintro _ ⟨x, hx, rfl⟩
      show e.symm (e x) ∈ P
      rw [e.symm_apply_apply]; exact hx))
    (by ext x; simp) (by ext x; simp)

theorem len_quot_semilinear {R R' M M' : Type*} [Ring R] [Ring R'] [AddCommGroup M] [Module R M]
    [AddCommGroup M'] [Module R' M'] {σ : R →+* R'} {σ' : R' →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
    (f : M →ₛₗ[σ] M') (hf : Function.Injective f) (A B : Submodule R M) :
    Module.length R (A ⧸ B.comap A.subtype) =
      Module.length R' (A.map f ⧸ (B.map f).comap (A.map f).subtype) := by
  let eA : A ≃ₛₗ[σ] A.map f := Submodule.equivMapOfInjective f hf A
  refine len_equiv_semilinear (quotEquivSL eA _ _ ?_)
  ext ⟨y, hy⟩
  simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.subtype_apply]
  constructor
  · rintro ⟨⟨x, hxA⟩, hxB, hxy⟩
    exact ⟨x, hxB, congrArg Subtype.val hxy⟩
  · rintro ⟨x, hxB, hfx⟩
    obtain ⟨x', hx'A, hx'⟩ := hy
    have hxx : x = x' := hf (hfx.trans hx'.symm)
    subst hxx
    refine ⟨⟨x, hx'A⟩, hxB, ?_⟩
    apply Subtype.ext
    exact hfx

theorem len_pi_sum {R : Type*} [CommRing R] {G : Type*} [Fintype G] [DecidableEq G] {M : G → Type*}
    [∀ g, AddCommGroup (M g)] [∀ g, Module R (M g)] (A B : ∀ g, Submodule R (M g)) :
    Module.length R ((Submodule.pi Set.univ A) ⧸
        (Submodule.pi Set.univ B).comap (Submodule.pi Set.univ A).subtype) =
      ∑ g, Module.length R (A g ⧸ (B g).comap (A g).subtype) := by
  classical
  let φ : (Submodule.pi Set.univ A) →ₗ[R] (∀ g, A g ⧸ (B g).comap (A g).subtype) :=
    LinearMap.pi (fun g => ((B g).comap (A g).subtype).mkQ ∘ₗ
      (((LinearMap.proj g).comp (Submodule.pi Set.univ A).subtype).codRestrict (A g)
        (fun x => x.2 g (Set.mem_univ g))))
  have hφ : Function.Surjective φ := by
    intro y
    choose x hx using fun g => Submodule.Quotient.mk_surjective _ (y g)
    refine ⟨⟨fun g => (x g : M g), fun g _ => (x g).2⟩, ?_⟩
    funext g
    rw [← hx g]
    rfl
  have hker : LinearMap.ker φ =
      (Submodule.pi Set.univ B).comap (Submodule.pi Set.univ A).subtype := by
    ext x
    simp only [LinearMap.mem_ker, Submodule.mem_comap, Submodule.subtype_apply, Submodule.mem_pi,
      Set.mem_univ, true_implies]
    rw [funext_iff]
    refine forall_congr' (fun g => ?_)
    change Submodule.Quotient.mk _ = 0 ↔ _
    rw [Submodule.Quotient.mk_eq_zero]
    rfl
  let e := (Submodule.quotEquivOfEq _ _ hker.symm).trans (φ.quotKerEquivOfSurjective hφ)
  rw [len_equiv_semilinear e]
  first
  | exact Module.length_pi
  | exact Module.length_pi_of_fintype _
  | simp [Module.length_pi]

end Formalism.L2.GlobalTheoryTheory.LemB
end
end

-- Source module: Formalism.LocalToGlobal.GlobalTheory.CoordinateLengths.LenLen2OfCoord

section

@[expose] public section

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LemB

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms NumberField MvPolynomial Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

variable (D : D7)

def owEquiv (w : D.what₂.places.Pl) : Ow D w ≃+* bwA_Ow D w :=
  Subring.equivMapOfInjective (intW D.what₂.places w) D.what₂.embLL D.what₂.embLL.injective

instance owPair (w : D.what₂.places.Pl) :
    RingHomInvPair ((owEquiv D w : Ow D w ≃+* bwA_Ow D w) : Ow D w →+* bwA_Ow D w)
      ((owEquiv D w).symm : bwA_Ow D w →+* Ow D w) :=
  RingHomInvPair.of_ringEquiv (owEquiv D w)

instance owPair' (w : D.what₂.places.Pl) :
    RingHomInvPair ((owEquiv D w).symm : bwA_Ow D w →+* Ow D w)
      ((owEquiv D w : Ow D w ≃+* bwA_Ow D w) : Ow D w →+* bwA_Ow D w) where
  comp_eq := by ext x; simp
  comp_eq₂ := by ext x; simp

variable (u : D.what₂.Word)

theorem lenLen2_of_coord (A : AtTTied u) (Lv : LvTied u A 0 (Nat.zero_le _)) (w : D.what₂.places.Pl) (hw : OverT D u w)
    (v : (D.mem u).A.vT)
    (hLc0 : ∀ c, clsCrd D u 0 (Nat.zero_le _) c ≤ Ld D u 0 (Nat.zero_le _) c)
    (B B' : (D.mem u).C.cls 0 → GL (Fin (D.R.N 0)) D.host.E)
    (hB : ∀ c, IsLocBasis (D.mem u).A.T (Ld D u 0 (Nat.zero_le _) c : Set _) (B c))
    (hB' : ∀ c, IsLocBasis (D.mem u).A.T (Lk A 0 (Nat.zero_le _) v c : Set _) (B' c))
    (hunit : ∀ c, (((((B c)⁻¹ * B' c : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E)).map
        (embT D ((D.fm u).tauOf w v))).det * (((D.mem u).A.T : ℂ))⁻¹ ∈ bwA_Ow D w ∧
      ((D.mem u).A.T : ℂ) * ((((((B c)⁻¹ * B' c : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E)).map
        (embT D ((D.fm u).tauOf w v))).det)⁻¹ ∈ bwA_Ow D w)
    (Φ : Vl D u 0 →ₛₗ[((owEquiv D w : Ow D w ≃+* bwA_Ow D w) : Ow D w →+* bwA_Ow D w)]
      ((D.mem u).C.cls 0 → MvPolynomial (D.what₂.Tau × Fin (D.R.N 0) × Fin (D.R.N 0)) ℂ))
    (hΦ : Function.Injective Φ)
    (hA : ((D.fm u).Bw 0 w v).map Φ = Submodule.pi Set.univ fun c =>
      ((intSubm D w ((D.fm u).lam 0)).map
            ((Formalism.L2.Forms.subP (bwA_N D ((D.fm u).tauOf w v) (B c) (B' c))).toLinearMap.restrictScalars (bwA_Ow D w))).map
          (scO (bwA_Ow D w) _ ((bwA_N D ((D.fm u).tauOf w v) (B c) (B' c) ((D.fm u).tauOf w v)).det ^
            ((D.fm u).lam 0 ((D.fm u).tauOf w v)).detShift)))
    (hS : (tL D u w ((D.fm u).bTop ((D.fm u).tauOf w v)) ((D.fm u).S 0 w)).map Φ = Submodule.pi Set.univ fun _ =>
      (intSubm D w ((D.fm u).lam 0)).map
            (scO (bwA_Ow D w) _ (((D.mem u).A.T : ℂ) ^ (D.fm u).bTop ((D.fm u).tauOf w v))))
    (hd : D.duS u = Fintype.card ((D.mem u).C.cls 0) *
      ∏ τ, Module.finrank ℤ (delSq ℤ (D.R.N 0) ((D.fm u).lam 0 τ))) :
    ∃ n : ℕ, len D u w ((D.fm u).Bw 0 w v) (tL D u w ((D.fm u).bTop ((D.fm u).tauOf w v)) ((D.fm u).S 0 w)) = n ∧
      (n : ℚ) = (D.what₂.places.ramIdx w : ℚ) * ((D.duS u : ℚ) *
        ((wsum ((D.fm u).lam 0 ((D.fm u).tauOf w v)) : ℚ) + (D.R.k : ℚ) * ((D.fm u).bTop ((D.fm u).tauOf w v) : ℚ)) /
          (D.R.k : ℚ)) := by
  classical
  have hkpos : (0 : ℚ) < (D.R.k : ℚ) := by
    have h := D.R.m_add_three_le_k
    exact_mod_cast (show 0 < D.R.k by omega)
  choose n hn hnq using fun c => cls_len_D D u A w hw v Lv c (hLc0 c) (B c) (B' c) (hB c) (hB' c) (hunit c)
  refine ⟨∑ c, n c, ?_, ?_⟩
  · unfold Formalism.MainNotions.product_first_zeroth_parts.len
    rw [len_quot_semilinear (σ' := ((owEquiv D w).symm : bwA_Ow D w →+* Ow D w)) Φ hΦ, hA, hS, len_pi_sum,
      Nat.cast_sum]
    exact Finset.sum_congr rfl fun c _ => hn c
  · have e : ∀ c, (n c : ℚ) = (D.what₂.places.ramIdx w : ℚ) *
        ((∏ τ, Module.finrank ℤ (delSq ℤ (D.R.N 0) ((D.fm u).lam 0 τ)) : ℕ) : ℚ) *
        ((wsum ((D.fm u).lam 0 ((D.fm u).tauOf w v)) : ℚ) + (D.R.k : ℚ) * ((D.fm u).bTop ((D.fm u).tauOf w v) : ℚ)) /
          (D.R.k : ℚ) := fun c => by
      rw [eq_div_iff hkpos.ne', mul_comm]; exact hnq c
    rw [Nat.cast_sum, Finset.sum_congr rfl fun c _ => e c, Finset.sum_const, Finset.card_univ, hd, nsmul_eq_mul]
    push_cast
    ring

end Formalism.L2.GlobalTheoryTheory.LemB
end
end
end

-- Source module: Formalism.LocalToGlobal.GlobalTheory.CoordinateLengths.IsCrdExists

section

@[expose] public section

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LemB

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms NumberField MvPolynomial Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

variable {D : D7} {u : D.what₂.Word}

def IsCrd (T : Forms0 D u) (B : GL (Fin (D.R.N 0)) D.host.E) (x : ((D.fm u).lat 0).V) (c : (D.mem u).C.cls 0)
    (Q : MvPolynomial (D.what₂.Tau × Fin (D.R.N 0) × Fin (D.R.N 0)) ℂ) : Prop :=
  ∀ z, (D.fm u).emb 0 x c z = fnOf (gramC (gramN D 0 (Nat.zero_le _)) (embT D)) (shiftOf (lamT u 0))
    (atInf (embT D) (B⁻¹ : GL (Fin (D.R.N 0)) D.host.E).1) Q (T.val0.eY z)

theorem atInf_unit (B : GL (Fin (D.R.N 0)) D.host.E) (τ : D.what₂.Tau) :
    IsUnit (atInf (embT D) (B : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) τ).det := by
  exact (Matrix.isUnit_iff_isUnit_det _).1 ((Units.isUnit B).map (RingHom.mapMatrix (embT D τ)))

theorem isCrd_unique (T : Forms0 D u) (B : GL (Fin (D.R.N 0)) D.host.E) (x : ((D.fm u).lat 0).V)
    (c : (D.mem u).C.cls 0) {Q Q' : MvPolynomial (D.what₂.Tau × Fin (D.R.N 0) × Fin (D.R.N 0)) ℂ}
    (h : IsCrd T B x c Q) (h' : IsCrd T B x c Q') : Q = Q' := by
  apply polynomial_function_frames_injective _ _ _ (atInf_unit (B⁻¹))
  funext y
  obtain ⟨z, rfl⟩ := T.val0.eY.surjective y
  rw [← h z, h' z]

theorem isCrd_exists (T : Forms0 D u) (B : GL (Fin (D.R.N 0)) D.host.E) (x : ((D.fm u).lat 0).V)
    (c : (D.mem u).C.cls 0) : ∃ Q, IsCrd T B x c Q := by
  obtain ⟨P, -, hP⟩ := ((T.val0.5 ((D.fm u).emb 0 x)).1 ⟨x, rfl⟩).2 c
  refine ⟨MvPolynomial.C (∏ τ, (atInf (embT D) (B : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) τ).det ^
      shiftOf (lamT u 0) τ) * subP (atInf (embT D) (B : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E)) P, fun z => ?_⟩
  have hN : (fun τ => atInf (embT D) (B : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) τ *
      atInf (embT D) (B⁻¹ : GL (Fin (D.R.N 0)) D.host.E).1 τ) = 1 := by
    funext τ
    simp only [atInf, ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _), Pi.one_apply]
  rw [hP z, ← fnOf_mul _ _ (atInf (embT D) (B : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E)), hN]

theorem isCrd_add (T : Forms0 D u) (B : GL (Fin (D.R.N 0)) D.host.E) {x y : ((D.fm u).lat 0).V}
    {c : (D.mem u).C.cls 0} {Q Q' : MvPolynomial (D.what₂.Tau × Fin (D.R.N 0) × Fin (D.R.N 0)) ℂ}
    (h : IsCrd T B x c Q) (h' : IsCrd T B y c Q') : IsCrd T B (x + y) c (Q + Q') := by
  intro z
  rw [map_add (f := _), Pi.add_apply, Pi.add_apply, h z, h' z, map_add (f := _), Pi.add_apply]

theorem isCrd_smul (T : Forms0 D u) (B : GL (Fin (D.R.N 0)) D.host.E) {x : ((D.fm u).lat 0).V}
    {c : (D.mem u).C.cls 0} {Q : MvPolynomial (D.what₂.Tau × Fin (D.R.N 0) × Fin (D.R.N 0)) ℂ}
    (h : IsCrd T B x c Q) (r : D.what₂.LL) : IsCrd T B (r • x) c (D.what₂.embLL r • Q) := by
  intro z
  rw [LinearMap.map_smulₛₗ, Pi.smul_apply, Pi.smul_apply, h z, map_smul, Pi.smul_apply]

def crd (T : Forms0 D u) (B : (D.mem u).C.cls 0 → GL (Fin (D.R.N 0)) D.host.E) (x : ((D.fm u).lat 0).V) :
    (D.mem u).C.cls 0 → MvPolynomial (D.what₂.Tau × Fin (D.R.N 0) × Fin (D.R.N 0)) ℂ :=
  fun c => Classical.choose (isCrd_exists T (B c) x c)

theorem crd_spec (T : Forms0 D u) (B : (D.mem u).C.cls 0 → GL (Fin (D.R.N 0)) D.host.E) (x : ((D.fm u).lat 0).V)
    (c : (D.mem u).C.cls 0) : IsCrd T (B c) x c (crd T B x c) :=
  Classical.choose_spec (isCrd_exists T (B c) x c)

theorem crd_eq (T : Forms0 D u) (B : (D.mem u).C.cls 0 → GL (Fin (D.R.N 0)) D.host.E) {x : ((D.fm u).lat 0).V}
    {c : (D.mem u).C.cls 0} {Q : MvPolynomial (D.what₂.Tau × Fin (D.R.N 0) × Fin (D.R.N 0)) ℂ}
    (h : IsCrd T (B c) x c Q) : crd T B x c = Q :=
  isCrd_unique T (B c) x c (crd_spec T B x c) h

theorem owEquiv_coe (w : D.what₂.places.Pl) (r : Ow D w) :
    ((((owEquiv D w : Ow D w ≃+* bwA_Ow D w) : Ow D w →+* bwA_Ow D w) r : bwA_Ow D w) : ℂ) =
      D.what₂.embLL (r : D.what₂.LL) := by
  rfl

theorem crd_add (T : Forms0 D u) (B : (D.mem u).C.cls 0 → GL (Fin (D.R.N 0)) D.host.E) (x y : ((D.fm u).lat 0).V) :
    crd T B (x + y) = crd T B x + crd T B y :=
  funext fun c => crd_eq T B (isCrd_add T (B c) (crd_spec T B x c) (crd_spec T B y c))

theorem crd_smul (T : Forms0 D u) (B : (D.mem u).C.cls 0 → GL (Fin (D.R.N 0)) D.host.E) (r : D.what₂.LL)
    (x : ((D.fm u).lat 0).V) (c : (D.mem u).C.cls 0) : crd T B (r • x) c = D.what₂.embLL r • crd T B x c :=
  crd_eq T B (isCrd_smul T (B c) (crd_spec T B x c) r)

def crdL (T : Forms0 D u) (B : (D.mem u).C.cls 0 → GL (Fin (D.R.N 0)) D.host.E) (w : D.what₂.places.Pl) :
    Vl D u 0 →ₛₗ[((owEquiv D w : Ow D w ≃+* bwA_Ow D w) : Ow D w →+* bwA_Ow D w)]
      ((D.mem u).C.cls 0 → MvPolynomial (D.what₂.Tau × Fin (D.R.N 0) × Fin (D.R.N 0)) ℂ) where
  toFun := crd T B
  map_add' x y := crd_add T B x y
  map_smul' r x := by
    funext c
    have h := crd_smul T B (r : D.what₂.LL) x c
    rw [Pi.smul_apply, Subring.smul_def r x, h, Subring.smul_def, owEquiv_coe]

theorem crdL_inj (T : Forms0 D u) (B : (D.mem u).C.cls 0 → GL (Fin (D.R.N 0)) D.host.E) (w : D.what₂.places.Pl) :
    Function.Injective (crdL T B w) := by
  intro x y hxy
  apply (D.fm u).emb_inj 0
  funext c z
  have hc : crd T B x c = crd T B y c := congrFun hxy c
  rw [crd_spec T B x c z, crd_spec T B y c z, hc]

end Formalism.L2.GlobalTheoryTheory.LemB
end
end
end
