module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AwayHomCompAlgebraMap
public import Mathlib.RingTheory.Ideal.Prime
public import Mathlib.RingTheory.Ideal.Span
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ApproximationQuotientsAgree
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DedekindPowerLocalization
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Etale.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleAwayQuotientEqLocalization
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorIntegerRingAlmostAllPlaces
import Mathlib.RingTheory.Etale.Pi
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueFieldAtPrimeIsSepClosedOfFiniteTypeStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ContrAtEqComapMap

section

@[expose] public section

namespace GlobalTheory.LocalSaturationContraction

variable {B : Type*} [CommRing B]

def satAt (b : B) (P : Ideal B) [hP : P.IsPrime] : Ideal B where
  carrier := {x | ∃ s, s ∉ P ∧ s * x ∈ Ideal.span {b}}
  zero_mem' := ⟨1, (Ideal.ne_top_iff_one P).1 hP.ne_top, by simp⟩
  add_mem' := by
    rintro x y ⟨s, hs, hx⟩ ⟨t, ht, hy⟩
    refine ⟨s * t, fun h => (hP.mem_or_mem h).elim hs ht, ?_⟩
    have : s * t * (x + y) = t * (s * x) + s * (t * y) := by ring
    rw [this]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hx) (Ideal.mul_mem_left _ _ hy)
  smul_mem' := by
    rintro c x ⟨s, hs, hx⟩
    refine ⟨s, hs, ?_⟩
    have : s * (c • x) = c * (s * x) := by rw [smul_eq_mul]; ring
    rw [this]
    exact Ideal.mul_mem_left _ _ hx

variable (b : B) (P : Ideal B) [P.IsPrime]

end GlobalTheory.LocalSaturationContraction
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleAwayQuotientEqLocalizationStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.away_quotient_span_eq_localization : ∀ (B D : Type) [CommRing B] [IsDedekindDomain B] [CommRing D] [Algebra B D] [Algebra.Etale B D] (f : B), f ≠ 0 → ∀ (P : Ideal B), P.IsMaximal → f ∈ P → ∀ (Q : Ideal D), Q.IsPrime → Q.comap (algebraMap B D) = P → (∀ d : D, ∃ b : B, d - algebraMap B D b ∈ Q) → ∃ g : D, (∀ a : Localization.Away g, ∃ b : B, a - algebraMap B (Localization.Away g) b ∈ Ideal.span {algebraMap B (Localization.Away g) f}) ∧ ∀ b : B, algebraMap B (Localization.Away g) b ∈ Ideal.span {algebraMap B (Localization.Away g) f} ↔ ∃ s : B, s ∉ P ∧ s * b ∈ Ideal.span {f} := by
  first | (exact @GlobalTheory.etale_away_quotient_eq_localization) | (exact GlobalTheory.etale_away_quotient_eq_localization) | (intros; apply GlobalTheory.etale_away_quotient_eq_localization  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleNeighbourhoodKillsClass

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

theorem _root_.GlobalTheory.T.etale_neighbourhood_kills_class : ∀ (q : ℕ) [NeZero q] (B : Type) [CommRing B], IsUnit (q : B) → ∀ (P : Ideal B) [P.IsMaximal], IsSepClosed (IsLocalRing.ResidueField (Localization.AtPrime P)) → ∀ (m i : ℤ), 0 < m → ∀ y : Ht q (sp B) m i, ∃ (D : Type) (_ : CommRing D) (_ : Algebra B D) (_ : Algebra.Etale B D) (Q : Ideal D), Q.IsPrime ∧ Q.comap (algebraMap B D) = P ∧ (∀ d : D, ∃ b : B, d - algebraMap B D b ∈ Q) ∧ pull _ (spMap (algebraMap B D)) _ _ y = 0 := by
  first | (exact @GlobalTheory.EtC.oneCoh_main) | (exact GlobalTheory.EtC.oneCoh_main) | (intros; apply GlobalTheory.EtC.oneCoh_main <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleProdOfEtale

section

@[expose] public section

namespace GlobalTheory.EtaleProd

abbrev fam (A₁ A₂ : Type) : Fin 2 → Type := ![A₁, A₂]

instance instCommRing (A₁ A₂ : Type) [CommRing A₁] [CommRing A₂] : ∀ i, CommRing (fam A₁ A₂ i) :=
  Fin.cases (inferInstanceAs (CommRing A₁)) (Fin.cases (inferInstanceAs (CommRing A₂)) finZeroElim)

instance instAlgebra (B A₁ A₂ : Type) [CommRing B] [CommRing A₁] [CommRing A₂] [Algebra B A₁] [Algebra B A₂] :
    ∀ i, Algebra B (fam A₁ A₂ i) :=
  Fin.cases (inferInstanceAs (Algebra B A₁)) (Fin.cases (inferInstanceAs (Algebra B A₂)) finZeroElim)

theorem etale_fam (B A₁ A₂ : Type) [CommRing B] [CommRing A₁] [CommRing A₂] [Algebra B A₁] [Algebra B A₂]
    (h₁ : Algebra.Etale B A₁) (h₂ : Algebra.Etale B A₂) : ∀ i, Algebra.Etale B (fam A₁ A₂ i) :=
  Fin.cases h₁ (Fin.cases h₂ finZeroElim)

end GlobalTheory.EtaleProd


open GlobalTheory.EtaleProd in
theorem GlobalTheory.etale_prod : ∀ (B A₁ A₂ : Type) [CommRing B] [CommRing A₁] [CommRing A₂] [Algebra B A₁] [Algebra B A₂], Algebra.Etale B A₁ → Algebra.Etale B A₂ → Algebra.Etale B (A₁ × A₂) := by
  intro B A₁ A₂ _ _ _ _ _ h₁ h₂
  haveI := etale_fam B A₁ A₂ h₁ h₂
  exact Algebra.Etale.of_equiv
    (AlgEquiv.ofRingEquiv (R := B) (f := RingEquiv.piFinTwo (fam A₁ A₂)) fun _ => rfl)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleProdOfEtaleStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.etale_prod_of_etale : ∀ (B A₁ A₂ : Type) [CommRing B] [CommRing A₁] [CommRing A₂] [Algebra B A₁] [Algebra B A₂], Algebra.Etale B A₁ → Algebra.Etale B A₂ → Algebra.Etale B (A₁ × A₂) := by
  first | (exact @GlobalTheory.etale_prod) | (exact GlobalTheory.etale_prod) | (intros; apply GlobalTheory.etale_prod <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalDensitiesBoundedAlmostAll

section

@[expose] public section

namespace GlobalTheory

theorem finite_maximal_ideals_containing (B : Type) [CommRing B] [IsDedekindDomain B] (f : B)
    (hf : f ≠ 0) : {P : Ideal B | P.IsMaximal ∧ f ∈ P}.Finite := by
  have hI : Ideal.span {f} ≠ (0 : Ideal B) := by
    rw [Ideal.zero_eq_bot, Ne, Ideal.span_singleton_eq_bot]; exact hf
  have hfin := Ideal.finite_factors hI
  apply (hfin.image (fun v : IsDedekindDomain.HeightOneSpectrum B => v.asIdeal)).subset
  rintro P ⟨hmax, hfP⟩
  have hne : P ≠ ⊥ := by
    rintro rfl
    exact hf ((Submodule.mem_bot B).mp hfP)
  refine ⟨⟨P, hmax.isPrime, hne⟩, ?_, rfl⟩
  show P ∣ Ideal.span {f}
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  exact hfP

theorem finite_maximal_ideals_containing' : ∀ (B : Type) [CommRing B] [IsDedekindDomain B] (f : B),
    f ≠ 0 → {P : Ideal B | P.IsMaximal ∧ f ∈ P}.Finite :=
  fun B _ _ f hf => finite_maximal_ideals_containing B f hf

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteMaximalContaining

section

@[expose] public section


theorem _root_.GlobalTheory.T.finite_maximal_containing : ∀ (B : Type) [CommRing B] [IsDedekindDomain B] (f : B), f ≠ 0 → {P : Ideal B | P.IsMaximal ∧ f ∈ P}.Finite := by
  first | (exact @GlobalTheory.finite_maximal_ideals_containing') | (exact GlobalTheory.finite_maximal_ideals_containing') | (intros; apply GlobalTheory.finite_maximal_ideals_containing' <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalVanishingCohomology

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GlobalTheory.AffineCurveNbhd

noncomputable section

namespace GlobalTheory.CurveNbhdKill

def locKer {B : Type} [CommRing B] (f : B) (P : Ideal B) (hP : P.IsPrime) : Ideal B :=
  GlobalTheory.LocalSaturationContraction.satAt f P (hP := hP)

theorem locKer_coprime {B : Type} [CommRing B] [IsDedekindDomain B] (f : B) (hf : f ≠ 0) (P P' : Ideal B)
    (hP : P.IsMaximal) (hP' : P'.IsMaximal) (hne : P ≠ P') :
    IsCoprime (locKer f P hP.isPrime) (locKer f P' hP'.isPrime) := by
  obtain ⟨N, hN⟩ := GlobalTheory.T.dedekind_power_localization B f hf P hP
  obtain ⟨N', hN'⟩ := GlobalTheory.T.dedekind_power_localization B f hf P' hP'
  have hc : IsCoprime P P' := Ideal.isCoprime_iff_sup_eq.2 (Ideal.IsMaximal.coprime_of_ne hP hP' hne)
  have hc' : IsCoprime (P ^ N) (P' ^ N') := hc.pow
  rw [Ideal.isCoprime_iff_sup_eq] at hc' ⊢
  exact eq_top_iff.2 (hc' ▸ sup_le_sup (fun b hb => hN b hb) (fun b hb => hN' b hb))

theorem mem_of_forall_locKer {B : Type} [CommRing B] (f b : B)
    (h : ∀ P : Ideal B, P.IsMaximal → f ∈ P → ∃ s : B, s ∉ P ∧ s * b ∈ Ideal.span {f}) :
    b ∈ Ideal.span {f} := by
  let J : Ideal B := Submodule.comap (LinearMap.mulRight B b) (Ideal.span {f})
  have hJ : J = ⊤ := by
    by_contra hne
    obtain ⟨M, hM, hJM⟩ := Ideal.exists_le_maximal J hne
    have hfJ : f ∈ J := by
      rw [Submodule.mem_comap, LinearMap.mulRight_apply]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self f)
    obtain ⟨s, hs, hsb⟩ := h M hM (hJM hfJ)
    exact hs (hJM (by rw [Submodule.mem_comap, LinearMap.mulRight_apply]; exact hsb))
  have h1 : (1 : B) ∈ J := hJ ▸ Submodule.mem_top
  simpa [J] using h1

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp [spMap, Spec.map_comp]

variable (q : ℕ) [NeZero q] (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B]
  [Algebra.FiniteType k B]

theorem onePoint (hq : IsUnit (q : k)) (f : B) (hf : f ≠ 0) (m i : ℤ) (hm : 1 ≤ m) (y : Ht q (sp B) m i)
    (P : Ideal B) (hP : P.IsMaximal) (hfP : f ∈ P) :
    ∃ (A : Type) (_ : CommRing A) (_ : Algebra B A) (_ : Algebra.Etale B A),
      (∀ a : A, ∃ b : B, a - algebraMap B A b ∈ Ideal.span {algebraMap B A f}) ∧
      (∀ b : B, algebraMap B A b ∈ Ideal.span {algebraMap B A f} ↔ b ∈ locKer f P hP.isPrime) ∧
      pull _ (spMap (algebraMap B A)) _ _ y = 0 := by
  have hqB : IsUnit (q : B) := by simpa using hq.map (algebraMap k B)
  have hsep := GlobalTheory.T.residueField_atPrime_isSepClosed_of_finiteType k B P
  obtain ⟨D, _, _, _, Q, hQ, hQP, hres, hy⟩ := GlobalTheory.T.etale_neighbourhood_kills_class q B hqB P hsep m i (by omega) y
  obtain ⟨g, hS, hK⟩ := GlobalTheory.T.away_quotient_span_eq_localization B D f hf P hP hfP Q hQ hQP hres
  refine ⟨Localization.Away g, inferInstance, inferInstance, inferInstance, hS, hK, ?_⟩
  rw [IsScalarTower.algebraMap_eq B D (Localization.Away g), spMap_comp', pull_comp, hy, map_zero]

theorem exists_nbhd_pull_eq_zero : ∀ (q : ℕ) [NeZero q] (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B], IsUnit (q : k) → ∀ f : B, f ≠ 0 → ¬ IsUnit f → ∀ (m i : ℤ), 1 ≤ m → ∀ y : Ht q (sp B) m i, ∃ (A' : Type) (_ : CommRing A') (_ : Algebra B A') (_ : Algebra.Etale B A'), IsNbhd B A' f ∧ pull _ (spMap (algebraMap B A')) _ _ y = 0 := by
  intro q _ k B _ _ _ _ _ _ hq f hf hfu m i hm y
  let Pt := {P : Ideal B // P.IsMaximal ∧ f ∈ P}
  haveI : Finite Pt := (GlobalTheory.T.finite_maximal_containing B f hf).to_subtype
  letI : Fintype Pt := Fintype.ofFinite Pt
  let K : Pt → Ideal B := fun x => locKer f x.1 x.2.1.isPrime
  have key : ∀ T : Finset Pt, T.Nonempty → ∃ (A : Type) (_ : CommRing A) (_ : Algebra B A) (_ : Algebra.Etale B A),
      (∀ a : A, ∃ b : B, a - algebraMap B A b ∈ Ideal.span {algebraMap B A f}) ∧
      (∀ b : B, algebraMap B A b ∈ Ideal.span {algebraMap B A f} ↔ b ∈ ⨅ x ∈ T, K x) ∧
      pull _ (spMap (algebraMap B A)) _ _ y = 0 := by
    intro T hT
    induction hT using Finset.Nonempty.cons_induction with
    | singleton x =>
      obtain ⟨A, _, _, _, hS, hK, hy⟩ := onePoint q k B hq f hf m i hm y x.1 x.2.1 x.2.2
      exact ⟨A, inferInstance, inferInstance, inferInstance, hS, fun b => by simpa [K] using hK b, hy⟩
    | cons x T hx hT ih =>
      obtain ⟨A₁, _, _, _, hS₁, hK₁, hy₁⟩ := ih
      obtain ⟨A₂, _, _, _, hS₂, hK₂, hy₂⟩ := onePoint q k B hq f hf m i hm y x.1 x.2.1 x.2.2
      have hcop : IsCoprime (⨅ j ∈ T, K j) (K x) := by
        refine (Ideal.isCoprime_biInf fun j hj => ?_).symm
        refine locKer_coprime f hf x.1 j.1 x.2.1 j.2.1 fun h => hx ?_
        have : x = j := Subtype.ext h
        exact this ▸ hj
      obtain ⟨hS, hK, hy⟩ := GlobalTheory.T.approximation_quotients_agree q B A₁ A₂ f _ _ m i y hcop hS₁ hK₁ hS₂ hK₂ hy₁ hy₂
      refine ⟨A₁ × A₂, inferInstance, inferInstance, GlobalTheory.T.etale_prod_of_etale B A₁ A₂ inferInstance inferInstance, hS, fun b => ?_, hy⟩
      rw [hK b, Finset.cons_eq_insert, Finset.iInf_insert, inf_comm]
  have hne : (Finset.univ : Finset Pt).Nonempty := by
    have hspan : Ideal.span {f} ≠ ⊤ := fun h => hfu (Ideal.span_singleton_eq_top.1 h)
    obtain ⟨M, hM, hfM⟩ := Ideal.exists_le_maximal _ hspan
    exact ⟨⟨M, hM, hfM (Ideal.mem_span_singleton_self f)⟩, Finset.mem_univ _⟩
  obtain ⟨A, _, _, _, hS, hK, hy⟩ := key Finset.univ hne
  refine ⟨A, inferInstance, inferInstance, inferInstance, ⟨hS, fun b hb => ?_⟩, hy⟩
  have hb' := (hK b).1 hb
  refine mem_of_forall_locKer f b fun P hP hfP => ?_
  have := (Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hb' ⟨P, hP, hfP⟩) (Finset.mem_univ _)
  exact this

end GlobalTheory.CurveNbhdKill

end
end
end
