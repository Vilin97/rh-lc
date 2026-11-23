module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.DvrFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.GalEmbTop
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.GradedFlagMoves.FlagMove
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.GradedFlagMoves.FlagNew
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RedIdeal
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
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Formalism.ConjugateSelfDual.Statement
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ZsmulGeneratorEqZeroOfProjection
public import Mathlib.Algebra.CharP.Lemmas
import ReciprocityTheory.GaloisValuations.GlobalA
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.DecompSigmaOrd
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.DecCyc
import Mathlib.Tactic.Linter.HaveILetI
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RedIdeal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.GradedFlagMoves.TameExp
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.GradedFlagMoves.ThetaEx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.GradedFlagMoves.UnipPow
import Mathlib.RingTheory.PicardGroup
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.GradedFlagMoves.MuTriv

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.Rt.muTriv :
    ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] (H : Subgroup Γ) (k : Type) [Field k] [CharP k l]
      (ψ : Γ →* k), IsLocallyConstant ψ → ∀ s ∈ muOf l H, ψ s = 1 := by
  intro l _ Γ _ _ _ H k _ _ ψ hψ s hs
  obtain ⟨-, a, ha⟩ := hs
  have hcl : IsClosed ((ψ.ker : Subgroup Γ) : Set Γ) := by
    have e : ((ψ.ker : Subgroup Γ) : Set Γ) = {x | ψ x = 1} := by
      ext x
      simp [MonoidHom.mem_ker]
    rw [e]
    exact hψ.isClosed_fiber 1
  have hle : ⁅H, H⁆ ≤ ψ.ker := by
    rw [Subgroup.commutator_le]
    intro g₁ _ g₂ _
    rw [MonoidHom.mem_ker, commutatorElement_def, map_mul, map_mul, map_mul]
    calc ψ g₁ * ψ g₂ * ψ g₁⁻¹ * ψ g₂⁻¹ = ψ (g₁ * g₁⁻¹) * ψ (g₂ * g₂⁻¹) := by
          rw [map_mul, map_mul]; ring
      _ = 1 := by simp
  have hm := Subgroup.topologicalClosure_minimal _ hle hcl ha
  rw [MonoidHom.mem_ker, map_pow] at hm
  have h0 : (ψ s - 1) ^ l ^ a = 0 := by
    rw [sub_pow_char_pow, hm, one_pow, sub_self]
  exact sub_eq_zero.mp (pow_eq_zero_iff (pow_ne_zero _ (Fact.out : l.Prime).ne_zero) |>.mp h0)
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.GradedFlagMoves.SplitMod

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.Rt.splitMod :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ w : ℕ, w.Prime →
      ∀ A : ValuationSubring Ω, A.valuation (w : Ω) < 1 → ¬ A.valuation (l : Ω) < 1 → Dec (F := ℚ) A ≤ D.om.ker → l ∣ w - 1 := by
  intro Ω _ _ _ l _ c D hD w hw A hwA hlA hdec
  have hlw : l ≠ w := by
    rintro rfl; exact hlA hwA
  obtain ⟨-, -, γ, hγ, -, hcyc⟩ := UpperTheory.V.Chr.decCyc Ω w A hw hwA
  have hγl : ((cycZ ℚ Ω l γ : ℤ_[l]ˣ) : ℤ_[l]) = w := hcyc l hlw
  have hom : D.om γ = 1 := hdec hγ
  have hbar := hD.om_bar γ
  simp only [Raw.bar, hom, chiO, MonoidHom.comp_apply, Units.coe_map, Units.val_one, map_one,
    MonoidHom.coe_coe, hγl] at hbar
  have hbar' : residue c.O (algebraMap ℤ_[l] c.O (w : ℤ_[l])) = 1 := hbar.symm
  have hint : Algebra.IsIntegral ℤ_[l] c.O := by
    haveI := c.fin
    infer_instance
  have key : ((w : ℤ_[l]) - 1) ∈ IsLocalRing.maximalIdeal ℤ_[l] := by
    have h0 : residue c.O (algebraMap ℤ_[l] c.O ((w : ℤ_[l]) - 1)) = 0 := by
      rw [map_sub, map_one, map_sub, map_one, hbar', sub_self]
    have hm := (IsLocalRing.residue_eq_zero_iff _).mp h0
    letI := hint
    have hmax : (IsLocalRing.maximalIdeal c.O).comap (algebraMap ℤ_[l] c.O) = IsLocalRing.maximalIdeal ℤ_[l] :=
      IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (IsLocalRing.maximalIdeal c.O))
    rw [← hmax]
    exact hm
  have hcast : ((w : ℤ_[l]) - 1) = (((w : ℤ) - 1 : ℤ) : ℤ_[l]) := by push_cast; rfl
  rw [hcast, IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits, PadicInt.norm_int_lt_one_iff_dvd] at key
  have h1 : ((w - 1 : ℕ) : ℤ) = (w : ℤ) - 1 := by
    rw [Nat.cast_sub hw.one_le, Nat.cast_one]
  rw [← h1] at key
  exact Int.natCast_dvd_natCast.mp key
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.RestrT

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

section SlopeTestRemainingChoices

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]

private theorem algCl (F : IntermediateField ℚ Ω) : IsAlgClosure F Ω := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : Algebra.IsAlgebraic F Ω := Algebra.IsAlgebraic.tower_top (K := ℚ) F
  exact ⟨inferInstance, inferInstance⟩

private theorem cont_resQ (F : IntermediateField ℚ Ω) [NumberField F] : Continuous (resQ F) := by
  haveI := algCl F
  exact (galEmbTop ℚ F Ω).1.continuous

private theorem cont_resLe {F F' : IntermediateField ℚ Ω} [NumberField F] [NumberField F'] (h : F ≤ F') :
    Continuous (resLe h) := by
  haveI := algCl F
  haveI := algCl F'
  rw [(galEmbTop ℚ F Ω).1.isInducing.continuous_iff]
  have e : (galEmb ℚ F Ω) ∘ (resLe h) = galEmb ℚ F' Ω := by
    funext g
    ext x
    rfl
  rw [e]
  exact (galEmbTop ℚ F' Ω).1.continuous

private theorem conj_dec {F : IntermediateField ℚ Ω} [NumberField F] {A A' : ValuationSubring Ω} {g s : G F Ω}
    (hA : ∀ x, g x ∈ A' ↔ x ∈ A) (hs : s ∈ Dec (F := F) A') : g⁻¹ * s * g ∈ Dec (F := F) A := by
  open scoped Pointwise in
  have hgA : g • A = A' := by
    ext x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ← hA, AlgEquiv.smul_def, ← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]
  have hs' : s • A' = A' := MulAction.mem_stabilizer_iff.mp hs
  show g⁻¹ * s * g ∈ MulAction.stabilizer (G F Ω) A
  rw [MulAction.mem_stabilizer_iff, mul_smul, mul_smul, hgA, hs', ← hgA, inv_smul_smul]

private theorem lc_of_cont {ι Γ k : Type} [Group Γ] [TopologicalSpace Γ] [Field k] {P : PD ι Γ k} (h : P.Cont ⊥) (i j : Fin 4) :
    IsLocallyConstant fun g => P.r g i j := by
  have hc := h i j 1
  refine IsLocallyConstant.desc _ (Ideal.Quotient.mk ((⊥ : Ideal k) ^ 1)) hc ?_
  intro x y hxy
  have h1 := Ideal.Quotient.eq.mp hxy
  rw [pow_one, Ideal.mem_bot, sub_eq_zero] at h1
  exact h1

private theorem lc_mat {ι Γ k : Type} [Group Γ] [TopologicalSpace Γ] [Field k] {P : PD ι Γ k} (h : P.Cont ⊥) :
    IsLocallyConstant P.r := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hij : ∀ i j, ∀ᶠ y in nhds x, P.r y i j = P.r x i j :=
    fun i j => (IsLocallyConstant.iff_eventually_eq _).mp (lc_of_cont h i j) x
  filter_upwards [Filter.eventually_all.mpr (fun i => Filter.eventually_all.mpr (hij i))] with y hy
  ext i j
  exact hy i j

variable {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c}

private theorem charP_of {k : Type} [Field k] (a : c.O →+* k) (ha : ∀ x ∈ maximalIdeal c.O, a x = 0) : CharP k l := by
  haveI := c.dvr
  haveI := c.fin
  have hp : l.Prime := Fact.out
  have hloc : IsLocalHom (algebraMap ℤ_[l] c.O) := (dvrFacts l c.O).2.2.1
  have hmem : (l : c.O) ∈ maximalIdeal c.O := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have hu' : IsUnit (algebraMap ℤ_[l] c.O (l : ℤ_[l])) := by simpa using hu
    have h2 : IsUnit ((l : ℤ_[l])) := (isUnit_map_iff (algebraMap ℤ_[l] c.O) _).mp hu'
    have h3 : (l : ℤ_[l]) ∈ nonunits ℤ_[l] := by
      rw [PadicInt.mem_nonunits, PadicInt.norm_p]
      exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)
    exact h3 h2
  have h0 : (l : k) = 0 := by
    have := ha _ hmem
    simpa using this
  exact (CharP.charP_iff_prime_eq_zero hp).mpr h0

private theorem chi_one {k : Type} [Field k] (a : c.O →+* k) (ha : ∀ x ∈ maximalIdeal c.O, a x = 0) (pr : Bool) {g : G ℚ Ω}
    (hg : D.rbar g = 1) (i : Fin 4) : a (chi D pr i g) = 1 := by
  show a ((D.ps (lab pr i) g : c.O)) = 1
  have hj : residue c.O ((D.ps (lab pr i) g : c.O)) = 1 := by
    have h1 := congrFun (congrFun hg (lab pr i)) (lab pr i)
    simpa [Raw.rbar, mapRep, Raw.r0, diagRep, Matrix.diagonal_apply_eq] using h1
  have hm : ((D.ps (lab pr i) g : c.O)) - 1 ∈ maximalIdeal c.O := by
    rw [← map_one (residue c.O)] at hj
    exact Ideal.Quotient.eq.mp hj
  have h2 := ha _ hm
  rw [map_sub, map_one, sub_eq_zero] at h2
  exact h2

private theorem killW (hD : D.Good) (T : Tower D) {k : Type} [Field k] (a : c.O →+* k) (ha : ∀ x ∈ maximalIdeal c.O, a x = 0)
    {W : Finset ℕ} {s : PD T.ι (G T.F Ω) k} (hs : (T.fr W).IsRes a s) (h5 : 5 ≤ l ∨ Supp qQ s.r) {w : ℕ} (hw : w.Prime)
    (hS : T.Splits w) {F' : IntermediateField ℚ Ω} (hd : Dies l w F') {A : ValuationSubring Ω} (hA : A.valuation (w : Ω) < 1)
    (hl : ¬ A.valuation (l : Ω) < 1) {g : G T.F Ω} (hg : g ∈ Ine (F := T.F) A) (hF : resQ T.F g ∈ F'.fixingSubgroup) :
    s.r g = 1 := by
  haveI := T.nF
  haveI : IsAlgClosure T.F Ω := algCl T.F
  have hlp : l.Prime := Fact.out
  haveI : CharP k l := charP_of a ha
  have hSp := hS A hA
  have hdec : ∀ σ ∈ Ine (F := T.F) A, resQ T.F σ ∈ Dec (F := ℚ) A := fun σ hσ => Ine_le_Dec (F := T.F) A hσ
  have hom : Dec (F := ℚ) A ≤ D.om.ker := fun x hx => (hSp hx).2
  have hwl : l ∣ w - 1 := Rt.splitMod D hD w hw A hA hl hom
  obtain ⟨θ0, hθo, hθu, hθne⟩ := Rt.thetaEx Ω l w hw hwl
  have hFθ := hd θ0 hθo hθu
  let φ : ↥(Ine (F := T.F) A) →* UpperTheory.V.GradeZeroInterpolatingElement.M4 k := s.r.comp (Ine (F := T.F) A).subtype
  let θ : ↥(Ine (F := T.F) A) →* Multiplicative (ZMod l) := (θ0.comp (resQ T.F)).comp (Ine (F := T.F) A).subtype
  have hφlc : IsLocallyConstant ⇑φ :=
    (lc_mat hs.cont).comp_continuous continuous_subtype_val
  have hφl : ∀ σ : ↥(Ine (F := T.F) A), φ σ ^ l = 1 := by
    intro σ
    apply Rt.unipPow k l
    · intro i
      have h1 := hs.res.diag σ.1 i
      have hr : D.rbar (resQ T.F σ.1) = 1 := (hSp (hdec σ.1 σ.2)).1.2
      rw [show φ σ i i = s.r σ.1 i i from rfl, h1]
      exact chi_one a ha T.pr hr i
    · rcases h5 with h5 | h5
      · left
        refine ⟨h5, ?_⟩
        rcases hs.res.shape with h | h
        · exact Or.inl (h.1 σ.1)
        · exact Or.inr (h σ.1)
      · right
        refine ⟨?_, h5 σ.1⟩
        have := hlp.two_le
        have := hD.l_odd
        omega
  have hθo' : IsOpen (θ.ker : Set ↥(Ine (F := T.F) A)) :=
    hθo.preimage ((cont_resQ T.F).comp continuous_subtype_val)
  have hθne' : θ ≠ 1 := by
    obtain ⟨g', hg'I, hg'⟩ := hθne A hA
    have hfix : g' ∈ T.F.fixingSubgroup := (hSp (Ine_le_Dec (F := ℚ) A hg'I)).1.1
    intro h
    let s' : G T.F Ω := IntermediateField.fixingSubgroupEquiv T.F ⟨g', hfix⟩
    have hs'I : s' ∈ Ine (F := T.F) A := hg'I
    have := DFunLike.congr_fun h ⟨s', hs'I⟩
    exact hg' this
  have hgθ : θ ⟨g, hg⟩ = 1 := hFθ hF
  exact Rt.tameExp T.F Ω l A hl (UpperTheory.V.GradeZeroInterpolatingElement.M4 k) φ hφlc hφl θ hθo' hθne' ⟨g, hg⟩ hgθ

end SlopeTestRemainingChoices

theorem UpperTheory.V.Ws.restrT :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ (T T' : Tower D) (hT : T.Le T'), T.Fit → ∀ (k : Type) [Field k] (a : c.O →+* k), (∀ x ∈ maximalIdeal c.O, a x = 0) → ∀ W : Finset ℕ, (∀ w ∈ W, w.Prime ∧ T.Splits w) → (∀ w ∈ W, Dies l w T'.F) →
      ∀ s : PD T.ι (G T.F Ω) k, (T.fr W).IsRes a s → (5 ≤ l ∨ Supp qQ s.r ∨ (T.fr ∅).IsRes a s) →
      ∃ s' : PD T'.ι (G T'.F Ω) k, (T'.fr ∅).IsRes a s' ∧ T.OverT hT s s' := by
  intro Ω _ _ _ l _ c D hD T T' hT hFit k _ a ha W hW hWd s hs h5
  haveI := T.nF
  haveI := T'.nF
  have hle : T.F ≤ T'.F := hT.le
  have hQ : ∀ g : G T'.F Ω, resQ T.F (resLe hle g) = resQ T'.F g := fun g => by
    ext x
    rfl
  have hcov : ∀ v' : T'.ι, ∃ v : T.ι, ∃ g : G T.F Ω, ∀ x, g x ∈ T'.pl v' ↔ x ∈ T.pl v := fun v' =>
    (T.cover (T'.pl v') (T'.ovl v')).exists
  choose bv bg hbg using hcov
  have hnew : ∀ v' : T'.ι, ∃ n', IsLow n' ∧ IsUp (adj n' * s.r (bg v') * s.n (bv v')) ∧
      (SuppM nP (s.r (bg v')) ∧ SuppM qQ (s.n (bv v')) → SuppM qQ n') := by
    intro v'
    apply Rt.flagNew k (a ↑(D.th (resQ T.F (bg v'))))
    · exact ((D.th (resQ T.F (bg v'))).isUnit.map a).ne_zero
    · exact hs.pair.mult (bg v')
    · exact hs.pair.low (bv v')
    · rcases hs.res.shape with ⟨h1, h2⟩ | h1
      · exact Or.inl ⟨h1 _, h2 _⟩
      · exact Or.inr (h1 _)
  choose nn hnlow hnup hnq using hnew
  have hconj : ∀ (v' : T'.ι) (t : G T.F Ω), t ∈ Dec (F := T.F) (T'.pl v') →
      (bg v')⁻¹ * t * bg v' ∈ Dec (F := T.F) (T.pl (bv v')) :=
    fun v' t ht => conj_dec (hbg v') ht
  have hmove : ∀ (v' : T'.ι) (t : G T.F Ω), t ∈ Dec (F := T.F) (T'.pl v') →
      IsUp (adj (nn v') * s.r t * nn v') ∧
      ∀ i, (adj (nn v') * s.r t * nn v') i i = s.ψ (bv v') i ((bg v')⁻¹ * t * bg v') := by
    intro v' t ht
    have hZ := hs.pair.flag (bv v') _ (hconj v' t ht)
    have key := Rt.flagMove k (s.r (bg v')) (s.r (bg v')⁻¹) (s.r ((bg v')⁻¹ * t * bg v'))
      (s.n (bv v')) (nn v') (by rw [← map_mul, mul_inv_cancel, map_one]) (hs.pair.low _) (hnlow v') (hnup v') hZ
    have e : s.r (bg v') * s.r ((bg v')⁻¹ * t * bg v') * s.r (bg v')⁻¹ = s.r t := by
      rw [← map_mul, ← map_mul]
      congr 1
      group
    rw [e] at key
    exact ⟨key.1, fun i => key.2 i⟩
  let s' : PD T'.ι (G T'.F Ω) k := ⟨s.r.comp (resLe hle), nn⟩
  have hcont : s'.Cont ⊥ := by
    intro i j N
    exact (hs.cont i j N).comp_continuous (cont_resLe hle)
  have hdiag : ∀ (g : G T'.F Ω) (i : Fin 4), s'.r g i i = a ↑(((T'.fr ∅).χ i) g) := by
    intro g i
    have := hs.res.diag (resLe hle g) i
    simp only [Tower.fr, MonoidHom.comp_apply] at this ⊢
    show s.r (resLe hle g) i i = _
    rw [this, hQ, hT.pr]
  have hchar : ∀ (v' : T'.ι), ∀ t ∈ (T'.fr ∅).Gv v', ∀ i, s'.ψ v' i t = a ↑(((T'.fr ∅).χ i) t) := by
    intro v' t ht i
    have ht' : resLe hle t ∈ Dec (F := T.F) (T'.pl v') := ht
    have h2 := (hmove v' _ ht').2 i
    have h3 := hs.res.char (bv v') _ (hconj v' _ ht') i
    show (adj (nn v') * s.r (resLe hle t) * nn v') i i = _
    rw [h2]
    refine h3.trans ?_
    simp only [Tower.fr, MonoidHom.comp_apply, map_mul, map_inv]
    rw [mul_comm _ ((chi D T.pr i) ((resQ T.F) (resLe hle t))), inv_mul_cancel_right, hQ, hT.pr]
  haveI := charP_of (c := c) a ha
  refine ⟨s', ⟨⟨?_, ?_, ?_, hnlow, ?_, ?_⟩, ⟨hdiag, hchar, ?_⟩, hcont⟩, ⟨rfl, ?_⟩⟩
  · intro g
    have := hs.pair.mult (resLe hle g)
    simp only [Tower.fr, MonoidHom.comp_apply] at this ⊢
    rw [hQ] at this
    exact this
  · rintro g ⟨A, hAw, hgI, hgr⟩
    show s.r (resLe hle g) = 1
    have hgI' : resLe hle g ∈ Ine (F := T.F) A := hgI
    have hgr' : D.rbar (resQ T.F (resLe hle g)) = 1 := by rw [hQ]; exact hgr
    have hlA : ¬ A.valuation (l : Ω) < 1 := hAw l (Finset.mem_insert_self _ _)
    rcases h5 with h5 | h5 | h5
    rotate_left 2
    · exact h5.pair.kill _ ⟨A, hAw, hgI', hgr'⟩
    all_goals
      by_cases hAW : Raw.Away (insert l W) A
      · exact hs.pair.kill _ ⟨A, hAW, hgI', hgr'⟩
      · simp only [Raw.Away, not_forall, not_not] at hAW
        obtain ⟨p, hp, hpA⟩ := hAW
        rcases Finset.mem_insert.mp hp with rfl | hpW
        · exact absurd hpA hlA
        · have hF : resQ T.F (resLe hle g) ∈ T'.F.fixingSubgroup := by
            rw [hQ, IntermediateField.mem_fixingSubgroup_iff]
            intro x hx
            exact g.commutes ⟨x, hx⟩
          exact killW hD T a ha hs (by first | exact Or.inl h5 | exact Or.inr h5) (hW p hpW).1 (hW p hpW).2 (hWd p hpW) hpA hlA hgI' hF
  · obtain ⟨j, hj⟩ := hT.g0
    have e : resLe hle T'.g0 = T.g0 ^ l ^ j := by
      ext x
      have := congrArg (fun σ : G ℚ Ω => σ x) (show resQ T.F (resLe hle T'.g0) = resQ T.F (T.g0 ^ l ^ j) by
        rw [hQ, hj, map_pow])
      exact this
    show Matrix.IsDiag (s.r (resLe hle T'.g0))
    rw [e, map_pow]
    have hd : Matrix.IsDiag (s.r T.g0) := hs.pair.nrm
    rw [Matrix.isDiag_iff_diagonal_diag] at hd
    rw [← hd, Matrix.diagonal_pow]
    exact Matrix.isDiag_diagonal _
  · intro v' t ht
    exact (hmove v' _ ht).1
  · intro v' t ht i
    refine (hchar v' t ht.1 i).trans ?_
    let ψh : G T'.F Ω →* k := a.toMonoidHom.comp ((Units.coeHom c.O).comp ((T'.fr ∅).χ i))
    have hlc : IsLocallyConstant ψh := by
      have := lc_of_cont hcont i i
      convert this using 1
      funext g
      exact (hdiag g i).symm
    exact Rt.muTriv l (G T'.F Ω) (Dec (F := T'.F) (T'.pl v')) k ψh hlc t ht
  · rcases hs.res.shape with ⟨h1, h2⟩ | h1
    · exact Or.inl ⟨fun g => h1 _, fun v' => hnq v' ⟨h1 _, h2 _⟩⟩
    · exact Or.inr (fun g => h1 _)
  · intro v'
    exact ⟨bv v', bg v', hbg v', hnup v'⟩
end
end
