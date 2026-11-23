module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
public import Formalism.SharpRestriction.Divisibility.LiftErrorLocal
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmissibleIndexBoundAllPowers
import Formalism.SharpRestriction.LevelLetterCocycles.IntegralHeckeForms
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.TypeStar
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsSplitOfMemAdmissibleConjugatePairPlaces
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

-- Source module: Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivSupOfIsotypicPartsInternalDirectSum

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.IntegralHeckeForms
open scoped TensorProduct

namespace GlobalTheory.SupLaw.Model

open GlobalTheory.TwAll

variable (D : D7)

abbrev Pt (j : ℕ) : Type := {_g : G0g D.nd // j ∈ Finset.Icc 1 D.R.m}

abbrev KK (i : D.ntw.Tw) : Type := FractionRing (D.ntw.O i)

variable (A : ∀ (i : D.ntw.Tw) (j : ℕ), ℕ → PlE D.host → Module.End (KK D i) (Pt D j → KK D i))
  (s : ∀ i : D.ntw.Tw, ℕ → KK D i)



end GlobalTheory.SupLaw.Model

end
end
end

-- Source module: Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MeetsReferenceOfMeetsAll

section

@[expose] public section

noncomputable section

namespace GlobalTheory.TwInputs.EigModel

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.IntegralHeckeForms Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open GlobalTheory.Triple (heckeVal satake muBase)

variable {D : D7}

variable {cf : CharFrame D} {Rw : RowSide D} {Sb : Finset (PlE D.host)} {eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0}

theorem sig_all_of (hN : NoFormsOff D) (hM : MeetsAll D) (hC : CommAll D)
    (hall : ∀ i, ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b ev, GlobalTheory.EigTie.IsEigSys D.nexp i j b ev →
      ∃ s : D.ntw.Sig i, D.ntw.jS i s = j ∧ D.ntw.side i s = b ∧ ∀ k P, HkIdx i k P → GlobalTheory.EigTie.sigEv s k P = ev k P) :
    D.nexp.sig_all := by
  intro i j b x ev hx he hk
  by_cases hj : j ∈ Finset.Icc 1 D.R.m
  · let W : Submodule (FractionRing (D.ntw.O i)) (D.nexp.Fm i j b) :=
      Eigsp D.nexp i j b ev ⊓ LinearMap.ker (eG D.nexp i j b - LinearMap.id)
    have mW : ∀ y, y ∈ W ↔ (∀ k P, HkIdx i k P → D.nexp.hkF i j b k P y = ev k P • y) ∧ eG D.nexp i j b y = y := by
      intro y
      simp only [W, Eigsp, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
        LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
    have hxW : x ∈ W := (mW x).2 ⟨fun k P h => hk k P h.1 h.2.1 h.2.2.1 h.2.2.2, he⟩
    have hst : GStable D.nexp i j b W := by
      intro g y hy
      obtain ⟨a, c⟩ := (mW y).1 hy
      refine (mW _).2 ⟨fun k P h => by rw [hC i j hj b k P h, a k P h, map_smul], ?_⟩
      have e := congrArg (MonoidAlgebra.lift (FractionRing (D.ntw.O i))
        (Module.End (FractionRing (D.ntw.O i)) (D.nexp.Fm i j b)) (G0g D.nd)
        (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp (D.nexp.actG i j b)))
        (D.nexp.eAlg_central i b (MonoidAlgebra.of _ _ g))
      rw [map_mul, map_mul, MonoidAlgebra.lift_of] at e
      have e2 := LinearMap.congr_fun e y
      change eG D.nexp i j b (D.nexp.actG i j b g y) = D.nexp.actG i j b g (eG D.nexp i j b y) at e2
      rw [e2, c]
    obtain ⟨y, ⟨hy1, hy2⟩, hy0⟩ := (Submodule.ne_bot_iff _).1
      (hM i j b W ((Submodule.ne_bot_iff _).2 ⟨x, hxW, hx⟩) hst fun y hy => ((mW y).1 hy).2)
    obtain ⟨a, c⟩ := (mW y).1 hy1
    obtain ⟨s, e1, e2, e3⟩ := hall i j hj b ev ⟨y, ⟨y, hy2, c⟩, hy0, a⟩
    exact ⟨s, e1, e2, fun k P p q r t => e3 k P ⟨p, q, r, t⟩⟩
  · exact absurd ((hN i j hj b).elim x 0) hx

section Laws

open GlobalTheory.SupLaw.Model

variable (D) (A : ∀ (i : D.ntw.Tw) (j : ℕ), ℕ → PlE D.host → Module.End (KK D i) (Pt D j → KK D i))
  (s : ∀ i : D.ntw.Tw, ℕ → KK D i)

end Laws

end GlobalTheory.TwInputs.EigModel

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodPartEigensystemIsTripleEigensystem

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwInputs.EigAll

theorem exists_smul_mem_of_mem_span {O K V : Type*} [CommRing O] [IsDomain O] [Field K] [Algebra O K]
    [IsFractionRing O K] [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V] (N : Submodule O V)
    {v : V} (hv : v ∈ Submodule.span K (N : Set V)) : ∃ d : O, d ≠ 0 ∧ d • v ∈ N := by
  let S : Submodule K V :=
    { carrier := {v | ∃ d : O, d ≠ 0 ∧ d • v ∈ N}
      add_mem' := by
        rintro a c ⟨d, hd, ha⟩ ⟨e, he, hc⟩
        refine ⟨d * e, mul_ne_zero hd he, ?_⟩
        rw [smul_add]
        refine N.add_mem ?_ ?_
        · rw [mul_comm, mul_smul]; exact N.smul_mem _ ha
        · rw [mul_smul]; exact N.smul_mem _ hc
      zero_mem' := ⟨1, one_ne_zero, by rw [smul_zero]; exact N.zero_mem⟩
      smul_mem' := by
        rintro c a ⟨d, hd, ha⟩
        obtain ⟨n, m, hm, rfl⟩ := IsFractionRing.div_surjective (A := O) c
        have hm0 : m ≠ 0 := nonZeroDivisors.ne_zero hm
        have hmK : algebraMap O K m ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hm
        refine ⟨m * d, mul_ne_zero hm0 hd, ?_⟩
        have e1 : m • ((algebraMap O K n / algebraMap O K m) • a) = n • a := by
          rw [← algebraMap_smul K m, smul_smul, mul_div_cancel₀ _ hmK, algebraMap_smul]
        show (m * d) • ((algebraMap O K n / algebraMap O K m) • a) ∈ N
        rw [mul_comm, mul_smul, e1, smul_comm]
        exact N.smul_mem _ ha }
  have hle : Submodule.span K (N : Set V) ≤ S :=
    Submodule.span_le.2 fun x hx => ⟨1, one_ne_zero, by rw [one_smul]; exact hx⟩
  exact hle hv

theorem eq_zero_of_joint {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    (T : ι → V →ₗ[K] V) (p : ι → Prop) (ev : ι → K) (M : Finset (ι → K)) :
    ∀ y : V, (∀ μ ∈ M, ∃ t, p t ∧ μ t ≠ ev t) → (∀ t, p t → T t y = ev t • y) →
      y ∈ Submodule.span K {z | ∃ μ ∈ M, ∀ t, p t → T t z = μ t • z} → y = 0 := by
  classical
  induction M using Finset.induction_on with
  | empty =>
    intro y _ _ hs
    have : {z : V | ∃ μ ∈ (∅ : Finset (ι → K)), ∀ t, p t → T t z = μ t • z} = ∅ := by
      ext z; simp
    rw [this, Submodule.span_empty, Submodule.mem_bot] at hs
    exact hs
  | insert μ0 M _ ih =>
    intro y hne hy hs
    obtain ⟨t0, hp0, hμ0⟩ := hne μ0 (Finset.mem_insert_self _ _)
    let L : V →ₗ[K] V := T t0 - μ0 t0 • LinearMap.id
    have hL : Submodule.span K {z | ∃ μ ∈ insert μ0 M, ∀ t, p t → T t z = μ t • z} ≤
        (Submodule.span K {z | ∃ μ ∈ M, ∀ t, p t → T t z = μ t • z}).comap L := by
      rw [Submodule.span_le]
      rintro z ⟨μ, hμ, hz⟩
      rw [SetLike.mem_coe, Submodule.mem_comap]
      rcases Finset.mem_insert.1 hμ with rfl | hμ
      · have : L z = 0 := by
          simp only [L, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, hz t0 hp0, sub_self]
        rw [this]; exact Submodule.zero_mem _
      · have : L z = (μ t0 - μ0 t0) • z := by
          simp only [L, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, hz t0 hp0, sub_smul]
        rw [this]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨μ, hμ, hz⟩)
    have hLy : L y = (ev t0 - μ0 t0) • y := by
      simp only [L, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, hy t0 hp0, sub_smul]
    have h0 := ih ((ev t0 - μ0 t0) • y) (fun μ hμ => hne μ (Finset.mem_insert_of_mem hμ))
      (fun t ht => by rw [map_smul, hy t ht, smul_comm]) (hLy ▸ hL hs)
    rcases smul_eq_zero.1 h0 with h | h
    · exact absurd (sub_eq_zero.1 h).symm hμ0
    · exact h

variable {D : D7} {cf : CharFrame D} {Rw : RowSide D} {low : Finset ℕ}
  {Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host} {S : RatDat D.ntw}
  {hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)} {eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0}
  {θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ}


open Classical in
def trEig (D : D7) (i : D.ntw.Tw) (j : ℕ) (b : Bool) : Set (D.nexp.Fm i j b) :=
  {z | ∃ μ ∈ (Finset.univ.filter fun s : D.ntw.Sig i => D.ntw.jS i s = j ∧ D.ntw.side i s = b).image
      (fun s (t : ℕ × PlE D.host) => GlobalTheory.EigTie.sigEv s t.1 t.2),
    ∀ t : ℕ × PlE D.host, HkIdx i t.1 t.2 → D.nexp.hkF i j b t.1 t.2 z = μ t • z}

theorem good_part_le_span_triple_eigenvectors (Bs : SideB D cf Rw low Pq S hL eig θ) (hF : FullAll D) (i : D.ntw.Tw) (j : ℕ)
    (hj : j ∈ Finset.Icc 1 D.R.m) (b : Bool) :
    V0 D.nexp i j b ≤ Submodule.span (FractionRing (D.ntw.O i)) (trEig D i j b) := by
  classical
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hj
  set K := FractionRing (D.ntw.O i)
  let Φ : K ⊗[D.ntw.O i] D.ntw.B i j b →ₗ[K] D.nexp.Fm i j b := (D.nexp.embB i j b).liftBaseChange K
  have hΦ : ∀ k P, HkIdx i k P → ∀ z, Φ (((D.ntw.hk i j b k P).baseChange K) z) = D.nexp.hkF i j b k P (Φ z) := by
    intro k P hP z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a x =>
      simp only [Φ, LinearMap.baseChange_tmul, LinearMap.liftBaseChange_tmul, map_smul]
      rw [Bs.hk_emb i j b k P x h1 h2 hP.2.2.2 hP.2.2.1 hP.2.1]
    | add z w hz hw => simp only [map_add (f := _), hz, hw]

  have hrange : ∀ x : D.ntw.B i j b, D.nexp.embB i j b x ∈ Submodule.span K (trEig D i j b) := by
    intro x
    have hx : (1 : K) ⊗ₜ[D.ntw.O i] x ∈ (⊤ : Submodule K (K ⊗[D.ntw.O i] D.ntw.B i j b)) := trivial
    rw [← Bs.sigSpan i j b h1 h2] at hx
    have hx' := Submodule.mem_map_of_mem (f := Φ) hx
    rw [Submodule.map_span] at hx'
    have e : Φ ((1 : K) ⊗ₜ[D.ntw.O i] x) = D.nexp.embB i j b x := by
      show (D.nexp.embB i j b).liftBaseChange K ((1 : K) ⊗ₜ[D.ntw.O i] x) = _
      rw [LinearMap.liftBaseChange_tmul, one_smul]
    rw [e] at hx'
    refine Submodule.span_mono ?_ hx'
    rintro _ ⟨z, ⟨s, hs1, hs2, hz⟩, rfl⟩
    refine ⟨fun t => GlobalTheory.EigTie.sigEv s t.1 t.2, Finset.mem_image.2 ⟨s, by simp [hs1, hs2], rfl⟩, ?_⟩
    intro t ht
    rw [← hΦ t.1 t.2 ht, hz t.1 t.2 ht.1 ht.2.1 ht.2.2.1 ht.2.2.2, map_smul]
    rfl
  intro v hv
  obtain ⟨d, hd, hdv⟩ := exists_smul_mem_of_mem_span (K := K) (D.nexp.Bsup i j b) (by rw [hF i j hj b]; trivial)
  have hdV : d • v ∈ V0 D.nexp i j b := by
    rw [← algebraMap_smul K d v]; exact Submodule.smul_mem _ _ hv
  have hmem : d • v ∈ LinearMap.range (D.nexp.embB i j b) := by
    rw [Bs.tw.B_range i j b]; exact ⟨hdv, hdV⟩
  obtain ⟨x, hx⟩ := hmem
  have hdK : algebraMap (D.ntw.O i) K d ≠ 0 := by
    intro h; exact hd (IsFractionRing.injective (D.ntw.O i) K (h.trans (map_zero _).symm))
  have : v = (algebraMap (D.ntw.O i) K d)⁻¹ • (d • v) := by
    rw [← algebraMap_smul K d v, smul_smul, inv_mul_cancel₀ hdK, one_smul]
  rw [this, ← hx]
  exact Submodule.smul_mem _ _ (hrange x)

theorem sig_all_of_sideB : ∀ (D : D7) (cf : CharFrame D) (Rw : RowSide D) (low : Finset ℕ)
    (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw)
    (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0)
    (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf Rw low Pq S hL eig θ),
    NoFormsOff D → MeetsAll D → CommAll D → FullAll D → D.nexp.sig_all := by
  intro D cf Rw low Pq S hL eig θ Bs hN hM hC hF
  classical
  refine EigModel.sig_all_of hN hM hC ?_
  rintro i j hj b ev ⟨y, hyV, hy0, hyE⟩
  by_contra hno
  push_neg at hno
  apply hy0
  refine eq_zero_of_joint (fun t : ℕ × PlE D.host => D.nexp.hkF i j b t.1 t.2) (fun t => HkIdx i t.1 t.2)
    (fun t => ev t.1 t.2) _ y ?_ (fun t ht => hyE t.1 t.2 ht) (good_part_le_span_triple_eigenvectors Bs hF i j hj b hyV)
  intro μ hμ
  obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hμ
  obtain ⟨hs1, hs2⟩ := (Finset.mem_filter.1 hs).2
  obtain ⟨k, P, hk, hne⟩ := hno s hs1 hs2
  exact ⟨(k, P), hk, hne⟩

end GlobalTheory.TwInputs.EigAll

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodPartEigensystemIsTripleEigensystemStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.good_part_eigensystem_is_triple_eigensystem : ∀ (D : D7) (cf : CharFrame D) (Rw : RowSide D) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf Rw low Pq S hL eig θ), NoFormsOff D → MeetsAll D → CommAll D → FullAll D → D.nexp.sig_all := by
  first | exact @GlobalTheory.TwInputs.EigAll.sig_all_of_sideB | exact GlobalTheory.TwInputs.EigAll.sig_all_of_sideB | (intros; apply GlobalTheory.TwInputs.EigAll.sig_all_of_sideB <;> assumption)
end
end
