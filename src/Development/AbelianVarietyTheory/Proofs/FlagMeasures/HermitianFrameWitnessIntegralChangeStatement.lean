module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.NormAdditiveCharacterTypePrimeEqOne
public import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameDualUnipotentGroupActsUnitriangularOnto
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUnipotentAddIsotropicToAnisotropicStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitriangularChangeFrameUnipotentStatement
import Mathlib.Tactic.Lemma

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsInnerLatticeVectorAnisotropic

section

@[expose] public section

open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG GlobalTheory.LocOver
open scoped Classical

namespace GlobalTheory.LocOver.InnerDual

theorem unif_mem_maximal {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
    (L : LocE F E) (ϖ : 𝒪[F]) (hϖ : Irreducible ϖ) (m : Ideal L.O) (hm : m.IsMaximal) :
    (⟨algebraMap F E ϖ, (GlobalTheory.UnramOrder.algebraMap_mem_iff L _).2 ϖ.2⟩ : L.O) ∈ m := by
  classical

  let φ : 𝒪[F] →+* L.O := ((algebraMap F E).comp (𝒪[F]).subtype).codRestrict L.O
    (fun c => (GlobalTheory.UnramOrder.algebraMap_mem_iff L c).2 c.2)
  have hcomp : (L.O.subtype).comp φ = algebraMap 𝒪[F] E := by
    ext c
    rfl
  have hint : φ.IsIntegral := by
    intro x
    obtain ⟨p, hp, hpx⟩ := (L.O_def x).1 x.2
    refine ⟨p, hp, Subtype.ext ?_⟩
    have key := Polynomial.hom_eval₂ p φ L.O.subtype x
    rw [hcomp] at key
    show L.O.subtype (Polynomial.eval₂ φ x p) = L.O.subtype 0
    rw [key, map_zero]
    exact hpx

  have := hm
  have hmax := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' φ hint m
  have h3 : ϖ ∈ m.comap φ := by
    rw [IsLocalRing.eq_maximalIdeal hmax]
    exact (IsLocalRing.mem_maximalIdeal ϖ).2 hϖ.not_isUnit
  exact Ideal.mem_comap.1 h3

end GlobalTheory.LocOver.InnerDual

namespace GlobalTheory.LocOver.InnerDual


open GlobalTheory.LocOver.UnipOnto in
theorem exists_inner_lattice_vector_anisotropic' : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E]
    [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type}
    [AddCommGroup V] [Module E V] (H : HermSp M V) (r : ℕ) (Fr : FrameD H r)
    (L : Submodule M.L.O (H.Wb Fr.f)), Fr.IsInner L → ∃ y : ↥(H.perp (H.X Fr.f)),
    H.mkW Fr.f y ∈ L ∧ H.h (Fr.f (Fin.last r)) (y : V) = 1 ∧ ∀ a, H.h (y : V) (Fr.es a) = 0 := by
  intro F _ _ _ E _ _ _ _ M hM V _ _ H r Fr L hL
  have : IsNonarchimedeanLocalField F := hM.loc
  have : CharZero F := hM.char0
  classical
  obtain ⟨_hfg, hdual, xz, hxz, hxzL, hprim⟩ := hL
  have hz : (xz : V) = Fr.f (Fin.last r) := hxz

  have hint : ∀ y : ↥(H.perp (H.X Fr.f)), H.mkW Fr.f y ∈ L →
      H.h (Fr.f (Fin.last r)) (y : V) ∈ M.L.O := by
    intro y hy
    have h0 := (hdual xz).1 hxzL y hy
    rwa [hz] at h0

  obtain ⟨I, hI⟩ : ∃ I : Ideal M.L.O, ∀ c : M.L.O, c ∈ I ↔
      ∃ y : ↥(H.perp (H.X Fr.f)), H.mkW Fr.f y ∈ L ∧ H.h (Fr.f (Fin.last r)) (y : V) = (c : E) :=
    ⟨{ carrier := {c | ∃ y : ↥(H.perp (H.X Fr.f)), H.mkW Fr.f y ∈ L ∧
          H.h (Fr.f (Fin.last r)) (y : V) = (c : E)}
       add_mem' := by
         rintro a b ⟨y, hy, hya⟩ ⟨y', hy', hyb⟩
         refine ⟨y + y', by rw [map_add (f := _)]; exact L.add_mem hy hy', ?_⟩
         show H.h _ ((y : V) + (y' : V)) = (a : E) + (b : E)
         rw [h_add_right, hya, hyb]
       zero_mem' := by
         refine ⟨0, by rw [map_zero]; exact L.zero_mem, ?_⟩
         show H.h _ (0 : V) = 0
         exact h_zero_right H _
       smul_mem' := by
         rintro c a ⟨y, hy, hya⟩
         refine ⟨M.L.cj (c : E) • y, ?_, ?_⟩
         · rw [map_smul]
           exact L.smul_mem ⟨M.L.cj (c : E), GlobalTheory.UnramOrder.cj_mem M.L c.2⟩ hy
         · show H.h _ (M.L.cj (c : E) • (y : V)) = (c : E) * (a : E)
           rw [h_smul_right, M.L.cj_cj, hya] },
     fun c => Iff.rfl⟩
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (R := 𝒪[F])
  have : IsPrincipalIdealRing M.L.O := (GlobalTheory.UnramOrder.order_facts M.L ϖ hϖ).2.2.2.1
  have hϖ0 : (ϖ : F) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)

  have htop : I = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hIm⟩ := Ideal.exists_le_maximal I hne
    obtain ⟨π, hπ⟩ := Submodule.IsPrincipal.principal m
    have hϖm := unif_mem_maximal M.L ϖ hϖ m hm
    rw [hπ, Submodule.mem_span_singleton] at hϖm
    obtain ⟨t, ht⟩ := hϖm
    have htE : (t : E) * (π : E) = algebraMap F E ϖ := congrArg Subtype.val ht
    obtain ⟨πi, hπi⟩ : ∃ πi : E, πi = (t : E) * algebraMap F E (ϖ : F)⁻¹ := ⟨_, rfl⟩
    have hinv : πi * (π : E) = 1 := by
      rw [hπi, mul_right_comm, htE, ← map_mul, mul_inv_cancel₀ hϖ0, map_one]
    have hvL : H.mkW Fr.f (πi • xz) ∈ L := by
      refine (hdual (πi • xz)).2 fun y hy => ?_
      have hyI : (⟨_, hint y hy⟩ : M.L.O) ∈ I := (hI _).2 ⟨y, hy, rfl⟩
      have hym := hIm hyI
      rw [hπ, Submodule.mem_span_singleton] at hym
      obtain ⟨s, hs⟩ := hym
      have hsE : (s : E) * (π : E) = H.h (Fr.f (Fin.last r)) (y : V) := congrArg Subtype.val hs
      show H.h (πi • (xz : V)) (y : V) ∈ M.L.O
      rw [H.h_smul_left, hz, ← hsE, mul_left_comm, hinv, mul_one]
      exact s.2
    have hxzv : H.mkW Fr.f xz = (π : E) • H.mkW Fr.f (πi • xz) := by
      refine Eq.trans ?_ (map_smul (H.mkW Fr.f) (π : E) (πi • xz))
      congr 1
      apply Subtype.ext
      show (xz : V) = (π : E) • (πi • (xz : V))
      rw [smul_smul, mul_comm, hinv, one_smul]
    have hu := hprim π (πi • xz) hvL hxzv
    exact hm.ne_top (hπ.trans (Ideal.span_singleton_eq_top.2 hu))
  have h1 : (1 : M.L.O) ∈ I := by
    rw [htop]
    exact Submodule.mem_top
  obtain ⟨y0, hy0L, hy0z⟩ := (hI 1).1 h1
  have hy0z' : H.h (Fr.f (Fin.last r)) (y0 : V) = 1 := hy0z

  obtain ⟨w, hw⟩ : ∃ w : V, w = ∑ a : Fin r, H.h (y0 : V) (Fr.es a) • Fr.f a.castSucc := ⟨_, rfl⟩
  have hwX : w ∈ H.X Fr.f := by
    rw [hw]
    exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Fj_le_X Fr _ (e_mem Fr a))
  have hwp : w ∈ H.perp (H.X Fr.f) := X_le_perp Fr hwX
  have hsumL : ∀ (g : Fin r → V) (u : V) (s : Finset (Fin r)),
      H.h (∑ a ∈ s, g a) u = ∑ a ∈ s, H.h (g a) u := by
    intro g u s
    refine Finset.induction_on s ?_ ?_
    · rw [Finset.sum_empty, Finset.sum_empty]
      exact H.h_zero_left u
    · intro a s ha ih
      rw [Finset.sum_insert ha, Finset.sum_insert ha, H.h_add_left, ih]
  refine ⟨y0 - ⟨w, hwp⟩, ?_, ?_, ?_⟩
  · have hmk0 : H.mkW Fr.f ⟨w, hwp⟩ = 0 := by
      exact (Submodule.Quotient.mk_eq_zero _).2 hwX
    rw [map_sub, hmk0, sub_zero]
    exact hy0L
  · show H.h _ ((y0 : V) - w) = 1
    rw [h_sub_right, h_right H _ w, pairing_isotropicSpan_lastVector Fr w hwX, map_zero, sub_zero, hy0z']
  · intro b
    show H.h ((y0 : V) - w) (Fr.es b) = 0
    rw [h_sub_left, hw, hsumL]
    simp [H.h_smul_left, Fr.h_es]

end GlobalTheory.LocOver.InnerDual
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsInnerLatticeVectorAnisotropicStatement

section

@[expose] public section

open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG GlobalTheory.LocOver
open scoped Classical

theorem _root_.GlobalTheory.T.exists_inner_lattice_vector_anisotropic : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r : ℕ) (Fr : FrameD H r) (L : Submodule M.L.O (H.Wb Fr.f)), Fr.IsInner L → ∃ y : ↥(H.perp (H.X Fr.f)), H.mkW Fr.f y ∈ L ∧ H.h (Fr.f (Fin.last r)) (y : V) = 1 ∧ ∀ a, H.h (y : V) (Fr.es a) = 0 := by
  first | exact @GlobalTheory.LocOver.InnerDual.exists_inner_lattice_vector_anisotropic' | exact GlobalTheory.LocOver.InnerDual.exists_inner_lattice_vector_anisotropic' | (intros; apply GlobalTheory.LocOver.InnerDual.exists_inner_lattice_vector_anisotropic' <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFrameWitnessIntegralChange

section

@[expose] public section

open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG GlobalTheory.LocOver
open scoped Classical

noncomputable section

namespace GlobalTheory.LocOver.WitChange

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r : ℕ}

lemma img_mul (g k : V ≃ₗ[E] V) (Λ : Submodule M.L.O V) : img (g * k) Λ = img g (img k Λ) := by
  ext v
  simp only [img, Submodule.mem_map, LinearMap.restrictScalars_apply, LinearEquiv.coe_coe,
    LinearEquiv.mul_apply]
  constructor
  · rintro ⟨u, hu, rfl⟩; exact ⟨k u, ⟨u, hu, rfl⟩, rfl⟩
  · rintro ⟨w, ⟨u, hu, rfl⟩, rfl⟩; exact ⟨u, hu, rfl⟩

lemma prF_e (Fr : FrameD H r) (a : Fin r) : Fr.prF (Fr.f a.castSucc) = 0 := by
  unfold FrameD.prF
  have h1 : ∑ c, H.h (Fr.f a.castSucc) (Fr.es c) • Fr.e c = Fr.f a.castSucc := by
    rw [Finset.sum_eq_single a]
    · rw [Fr.h_es, if_pos rfl, one_smul]; rfl
    · intro c _ hc; rw [Fr.h_es, if_neg (Ne.symm hc), zero_smul]
    · intro h; exact absurd (Finset.mem_univ a) h
  have h2 : ∑ c, H.h (Fr.f a.castSucc) (Fr.e c) • Fr.es c = 0 :=
    Finset.sum_eq_zero (fun c _ => by
      show H.h (Fr.f a.castSucc) (Fr.f c.castSucc) • Fr.es c = _
      rw [Fr.h_iso _ _ (Or.inl (Fin.castSucc_lt_last a).ne), zero_smul])
  rw [h1, h2]; simp

lemma frame_projection_last_eq_self (Fr : FrameD H r) : Fr.prF (Fr.f (Fin.last r)) = Fr.f (Fin.last r) := by
  unfold FrameD.prF
  have h1 : ∑ c, H.h (Fr.f (Fin.last r)) (Fr.es c) • Fr.e c = 0 :=
    Finset.sum_eq_zero (fun c _ => by rw [H.h_herm (Fr.es c) _, Fr.h_sz, map_zero, zero_smul])
  have h2 : ∑ c, H.h (Fr.f (Fin.last r)) (Fr.e c) • Fr.es c = 0 :=
    Finset.sum_eq_zero (fun c _ => by
      show H.h (Fr.f (Fin.last r)) (Fr.f c.castSucc) • Fr.es c = _
      rw [Fr.h_iso _ _ (Or.inr (Fin.castSucc_lt_last c).ne), zero_smul])
  rw [h1, h2]; simp

lemma frame_mem (Fr : FrameD H r) {L : Submodule M.L.O (H.Wb Fr.f)} (hL : Fr.IsInner L) (b : Fin (r + 1)) :
    Fr.f b ∈ Fr.LamStd L := by
  apply Formalism.MainNotions.BridgeLemma.f_mem_LamStd <;> assumption

end

theorem integral_change {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    {M : Model F E} (hOK : M.OK) {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r : ℕ}
    (Fr : FrameD H r) (L : Submodule M.L.O (H.Wb Fr.f)) (hL : Fr.IsInner L)
    (A : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (hA : Uni A) (hAO : ∀ a b, A a b ∈ M.L.O) :
    ∃ k ∈ Fr.N, (∀ b, k (Fr.f b) = ∑ a, A a b • Fr.f a) ∧ img k (Fr.LamStd L) = Fr.LamStd L := by
  obtain ⟨kl, hkl, hkle, hklz, hklL⟩ := GlobalTheory.T.unitriangular_change_frame_unipotent M hOK H r Fr L A hA hAO
  obtain ⟨y, hyL, hyz, hyes⟩ := GlobalTheory.T.exists_inner_lattice_vector_anisotropic M hOK H r Fr L hL
  have hx : ∑ a : Fin r, A a.castSucc (Fin.last r) • Fr.f a.castSucc ∈
      Submodule.span M.L.O (Set.range fun a : Fin r => Fr.f a.castSucc) :=
    Submodule.sum_mem _ fun a _ =>
      Submodule.smul_mem _ (⟨A a.castSucc (Fin.last r), hAO _ _⟩ : M.L.O) (Submodule.subset_span ⟨a, rfl⟩)
  obtain ⟨kz, hkz, hkzz, hkzX, hkzL⟩ := GlobalTheory.T.exists_unipotent_add_isotropic_to_anisotropic M hOK H r Fr L hL y hyL hyz hyes _ hx
  refine ⟨kz * kl, mul_mem hkz hkl, fun b => ?_, by rw [img_mul, hklL, hkzL]⟩
  induction b using Fin.lastCases with
  | last =>
    rw [LinearEquiv.mul_apply, hklz, hkzz, Fin.sum_univ_castSucc, hA.2, one_smul, add_comm]
  | cast c =>
    rw [LinearEquiv.mul_apply, hkle c]
    apply hkzX
    rw [Fin.sum_univ_castSucc, hA.1 _ _ (Fin.castSucc_lt_last c), zero_smul, add_zero]
    exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

theorem witness_change : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r : ℕ), ∀ (k : ℕ) (P : FPair H r), Module.finrank E V = k + 2 * r + 1 → P.RelG (theta M) → ∀ (d : Datum P) (t : Term V M r), IsTermOver P d t → ∀ (A A' : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (g g' : Fin (r + 1) → V), Uni A → Uni A' → (∀ a b, A a b ∈ M.L.O ∧ A' a b ∈ M.L.O ∧ A a b - A' a b ∈ Submodule.span M.L.O {algebraMap F E (theta M)}) → Chg t.f A g → Chg t.f' A' g' → IsTermOver P d ⟨t.abelian₂, g, g', t.T, t.T'⟩ := by
  intro F _ _ _ E _ _ _ _ M hOK V _ _ H r k P hk hrel d t ht A A' g g' hA hA' hAA hg hg'
  obtain ⟨hT, hT', ⟨n, hn, hf, hLam⟩, ⟨n', hn', hf', hLam'⟩, hadm⟩ := ht
  obtain ⟨kA, hkA, hkAf, hkAL⟩ := integral_change hOK P.A d.L d.hL A hA (fun a b => (hAA a b).1)
  obtain ⟨kB, hkB, hkBf, hkBL⟩ := integral_change hOK P.B d.L' d.hL' A' hA' (fun a b => (hAA a b).2.1)
  have hfΛ : ∀ a, t.f a ∈ t.abelian₂ := by
    intro a; rw [hf, hLam]; exact ⟨P.A.f a, frame_mem P.A d.hL a, rfl⟩
  refine ⟨hT, hT', ⟨n * kA, mul_mem hn hkA, ?_, ?_⟩, ⟨n' * kB, mul_mem hn' hkB, ?_, ?_⟩, ?_⟩
  · funext b
    show g b = n (kA (P.A.f b))

    rw [hg b, hkAf b, map_sum, hf]
    simp only [map_smul]
  · show t.abelian₂ = _
    rw [img_mul, hkAL, hLam]
  · funext b
    show g' b = n' (kB (P.B.f b))

    rw [hg' b, hkBf b, map_sum, hf']
    simp only [map_smul]
  · show t.abelian₂ = _
    rw [img_mul, hkBL, hLam']
  · intro gg hgg
    obtain ⟨had, hio⟩ := hadm gg hgg
    refine ⟨fun b => ?_, hio⟩
    have hθ : theta M = (gg.q : F) := by simp [theta, hgg]
    show g' b - g b ∈ H.smulLat (algebraMap F E (gg.q : F)) t.abelian₂
    have e1 : g' b - g b = ∑ a, (A' a b • (t.f' a - t.f a) - (A a b - A' a b) • t.f a) := by
      rw [hg b, hg' b, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      simp only [smul_sub, sub_smul]; abel
    rw [e1]
    refine Submodule.sum_mem _ fun a _ => Submodule.sub_mem _ ?_ ?_
    · exact Submodule.smul_mem _ (⟨A' a b, (hAA a b).2.1⟩ : M.L.O) (had a)
    · obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 (hAA a b).2.2
      rw [hθ] at hc
      rw [← hc]
      have h1 : algebraMap F E (gg.q : F) • t.f a ∈ H.smulLat (algebraMap F E (gg.q : F)) t.abelian₂ :=
        Submodule.subset_span ⟨t.f a, hfΛ a, rfl⟩
      rw [smul_assoc]
      exact Submodule.smul_mem _ c h1

end GlobalTheory.LocOver.WitChange
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFrameWitnessIntegralChangeStatement

section

@[expose] public section

open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG GlobalTheory.LocOver
open scoped Classical

theorem _root_.GlobalTheory.T.hermitian_frame_witness_integral_change : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r : ℕ), ∀ (k : ℕ) (P : FPair H r), Module.finrank E V = k + 2 * r + 1 → P.RelG (theta M) → ∀ (d : Datum P) (t : Term V M r), IsTermOver P d t → ∀ (A A' : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (g g' : Fin (r + 1) → V), Uni A → Uni A' → (∀ a b, A a b ∈ M.L.O ∧ A' a b ∈ M.L.O ∧ A a b - A' a b ∈ Submodule.span M.L.O {algebraMap F E (theta M)}) → Chg t.f A g → Chg t.f' A' g' → IsTermOver P d ⟨t.abelian₂, g, g', t.T, t.T'⟩ := by
  first | exact @GlobalTheory.LocOver.WitChange.witness_change | exact GlobalTheory.LocOver.WitChange.witness_change | (intros; apply GlobalTheory.LocOver.WitChange.witness_change <;> assumption)
end
end
