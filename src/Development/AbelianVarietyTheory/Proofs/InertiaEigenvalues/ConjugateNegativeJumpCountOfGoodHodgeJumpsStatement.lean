module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TripleAtt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsComplexReadingLocalEmbedding
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
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfForallMemFilV
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsComplexReadingLocalEmbeddingStatement

section

@[expose] public section

open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

theorem _root_.GlobalTheory.T.exists_complex_reading_local_embedding : ∀ (D : D7) (bkP : BlochKatoReduction.BK D) (i : D.ntw.Tw) (ι : FractionRing (D.ntw.O0 i) →+* ℂ) (v : HeightOneSpectrum (𝓞 D.host.E)) (hv : v ∈ placesOver D.host.E (D.ntw.l i)) (τ : EmbV bkP i v hv), ∃ τc : D.host.E →+* ℂ, ReadEmb bkP i ι v hv τ τc ∧ ∀ (v' : HeightOneSpectrum (𝓞 D.host.E)) (hv' : v' ∈ placesOver D.host.E (D.ntw.l i)) (τ' : EmbV bkP i v' hv'), IsConjEmb bkP i v v' hv hv' τ τ' → ReadEmb bkP i ι v' hv' τ' (τc.comp (cj D)) := by
  first | exact @GlobalTheory.ReadEmbEx.exists_readEmb | exact GlobalTheory.ReadEmbEx.exists_readEmb | (intros; apply GlobalTheory.ReadEmbEx.exists_readEmb <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankDdRAndFilZeroOfJumpMultiset

section

@[expose] public section

namespace GlobalTheory.JumpDims

open Module
open scoped TensorProduct

section Linear

variable {L U : Type} [Field L] [AddCommGroup U] [Module L U]

theorem exists_le_of_exh (D : Submodule L U) [FiniteDimensional L D] (F : ℤ → Submodule L U)
    (hanti : Antitone F) (hexh : ∀ x, ∃ a, x ∈ F a) : ∃ a, D ≤ F a := by
  obtain ⟨S, hS⟩ : D.FG := Module.Finite.iff_fg.mp inferInstance
  choose n hn using hexh
  obtain ⟨a, ha⟩ := (S.image n).bddBelow
  refine ⟨a, ?_⟩
  rw [← hS, Submodule.span_le]
  intro x hx
  exact hanti (ha (Finset.mem_coe.mpr (Finset.mem_image_of_mem n hx))) (hn x)

theorem exists_inf_eq_bot_of_sep (D : Submodule L U) [FiniteDimensional L D] (F : ℤ → Submodule L U)
    (hanti : Antitone F) (hsep : ∀ x, (∀ a, x ∈ F a) → x = 0) : ∃ a, D ⊓ F a = ⊥ := by
  have hfin : ∀ a, FiniteDimensional L ↥(D ⊓ F a) := fun a =>
    Submodule.finiteDimensional_of_le inf_le_left
  let a : ℤ := Function.argmin (fun a : ℤ => finrank L ↥(D ⊓ F a))
  have ha : ∀ b, finrank L ↥(D ⊓ F a) ≤ finrank L ↥(D ⊓ F b) := fun b =>
    Function.argmin_le (fun a : ℤ => finrank L ↥(D ⊓ F a)) b
  refine ⟨a, eq_bot_iff.mpr fun x hx => ?_⟩
  rw [Submodule.mem_bot]
  refine hsep x fun b => ?_
  rcases le_total a b with h | h
  · have : D ⊓ F b = D ⊓ F a :=
      Submodule.eq_of_le_of_finrank_le (inf_le_inf_left D (hanti h)) (ha b)
    exact (this ▸ hx : x ∈ D ⊓ F b).2
  · exact hanti h hx.2

theorem card_filter_succ (M : Multiset ℤ) (a : ℤ) :
    Multiset.card (M.filter (a ≤ ·)) = Multiset.card (M.filter (a + 1 ≤ ·)) + M.count a := by
  induction M using Multiset.induction_on with
  | empty => simp
  | cons b M ih =>
    rw [Multiset.filter_cons, Multiset.filter_cons, Multiset.count_cons, Multiset.card_add,
      Multiset.card_add, ih]
    split_ifs <;> simp <;> omega

theorem finrank_of_mult (D : Submodule L U) [FiniteDimensional L D] (F : ℤ → Submodule L U)
    (hanti : Antitone F) (hexh : ∀ x, ∃ a, x ∈ F a) (hsep : ∀ x, (∀ a, x ∈ F a) → x = 0)
    (M : Multiset ℤ)
    (hM : ∀ a, (finrank L ↥(D ⊓ F a) : ℤ) - finrank L ↥(D ⊓ F (a + 1)) = (M.count a : ℤ)) :
    finrank L D = Multiset.card M ∧
      ∀ a, finrank L ↥(D ⊓ F a) = Multiset.card (M.filter (a ≤ ·)) := by
  let g : ℤ → ℤ := fun a => (finrank L ↥(D ⊓ F a) : ℤ) - Multiset.card (M.filter (a ≤ ·))
  have hstep : ∀ a, g (a + 1) = g a := fun a => by
    have h1 := hM a
    have h2 := card_filter_succ M a
    simp only [g]
    omega
  have hconst : ∀ a, g a = g 0 := fun a => by
    induction a using Int.induction_on with
    | zero => rfl
    | succ n ih => rw [hstep, ih]
    | pred n ih => rw [← ih, ← hstep]; congr 1; ring
  obtain ⟨hi, hhi⟩ := exists_inf_eq_bot_of_sep D F hanti hsep
  obtain ⟨lo, hlo⟩ := exists_le_of_exh D F hanti hexh
  obtain ⟨u, hu⟩ := M.toFinset.bddAbove
  obtain ⟨l, hl⟩ := M.toFinset.bddBelow
  have hu' : ∀ x ∈ M, x ≤ u := fun x hx => hu (by simpa using hx)
  have hl' : ∀ x ∈ M, l ≤ x := fun x hx => hl (by simpa using hx)
  have h0 : g (max hi (u + 1)) = 0 := by
    have e1 : D ⊓ F (max hi (u + 1)) = ⊥ :=
      eq_bot_iff.mpr (hhi ▸ inf_le_inf_left D (hanti (le_max_left _ _)))
    have e2 : M.filter (max hi (u + 1) ≤ ·) = 0 :=
      Multiset.filter_eq_nil.mpr fun x hx h => by
        have := hu' x hx
        have := le_max_right hi (u + 1)
        omega
    show (finrank L ↥(D ⊓ F (max hi (u + 1))) : ℤ) - Multiset.card (M.filter (max hi (u + 1) ≤ ·)) = 0
    rw [e1, e2]
    simp
  have hall : ∀ a, finrank L ↥(D ⊓ F a) = Multiset.card (M.filter (a ≤ ·)) := fun a => by
    have : g a = 0 := by rw [hconst a, ← hconst (max hi (u + 1)), h0]
    simp only [g] at this
    omega
  refine ⟨?_, hall⟩
  have e1 : D ⊓ F (min lo l) = D := inf_eq_left.mpr (hlo.trans (hanti (min_le_left _ _)))
  have e2 : M.filter (min lo l ≤ ·) = M :=
    Multiset.filter_eq_self.mpr fun x hx => (min_le_right _ _).trans (hl' x hx)
  have := hall (min lo l)
  rwa [e1, e2] at this

end Linear

open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

theorem finite_of_isdR {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
    {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (Bw : LocBridge l E Ω Gw O) (P : LocPrime l) {m : ℕ}
    (r : ↥Gw →* Matrix.GeneralLinearGroup (Fin m) O) (h : Bw.IsdRW P r) :
    FiniteDimensional ↥Bw.LL.1 ↥(Formalism.WeaklyAdmissibleFiltrations.DdR (P.PD Bw.Kw) (Bw.rep r)) := by
  set_option synthInstance.maxHeartbeats 200000 in
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · haveI : Subsingleton (Formalism.WeaklyAdmissibleFiltrations.DdR (P.PD Bw.Kw) (Bw.rep r)) := by
      refine ⟨fun x y => Subtype.ext ?_⟩
      have hz : ∀ z : (Fin 0 → ↥Bw.LL.1) ⊗[ℚ_[l]] P.R.BdR, z = 0 := fun z => by
        induction z using TensorProduct.induction_on with
        | zero => rfl
        | tmul a b => rw [Subsingleton.elim a 0, TensorProduct.zero_tmul]
        | add a b ha hb => rw [ha, hb, add_zero]
      rw [hz x.1, hz y.1]
    haveI : Finite (Formalism.WeaklyAdmissibleFiltrations.DdR (P.PD Bw.Kw) (Bw.rep r)) := Finite.of_subsingleton
    exact Module.Finite.of_finite
  · haveI := (P.PD Bw.Kw).finK
    haveI : Module.Free ↥Bw.LL.1 ↥(Formalism.WeaklyAdmissibleFiltrations.DdR (P.PD Bw.Kw) (Bw.rep r)) := Module.Free.of_divisionRing _ _
    exact Module.finite_of_finrank_pos (by rw [h]; exact Nat.mul_pos Module.finrank_pos hm)

theorem dims_of_mult : ∀ (D : D7) (bkP : BlochKatoReduction.BK D) (i : D.ntw.Tw) (s : D.ntw.Sig i), ∀ (v : HeightOneSpectrum (𝓞 D.host.E)) (hv : v ∈ placesOver D.host.E (D.ntw.l i)) (τ : EmbV bkP i v hv) (M : Multiset ℤ), HodgeL bkP i s → (∀ a : ℤ, Formalism.WeaklyAdmissibleFiltrations.multV (PDv bkP i v hv) (repV bkP i v hv (Tgl i s)) τ a = (M.count a : ℤ)) → dimD bkP i v hv (Tgl i s) τ = Multiset.card M ∧ dimFil0 bkP i v hv (Tgl i s) τ = Multiset.card (M.filter (0 ≤ ·)) := by
  set_option synthInstance.maxHeartbeats 200000 in
  intro D bkP i s v hv τ M hH hM
  have hdR := (hH v hv (Tgl i s) (Or.inr rfl)).1
  haveI := finite_of_isdR _ _ _ hdR
  haveI : FiniteDimensional _ ↥(Formalism.WeaklyAdmissibleFiltrations.DdRE (PDv bkP i v hv) (repV bkP i v hv (Tgl i s)) τ) :=
    Submodule.finiteDimensional_of_le (S₂ := Formalism.WeaklyAdmissibleFiltrations.DdR (PDv bkP i v hv) (repV bkP i v hv (Tgl i s)))
      inf_le_left
  have key := finrank_of_mult (Formalism.WeaklyAdmissibleFiltrations.DdRE (PDv bkP i v hv) (repV bkP i v hv (Tgl i s)) τ)
    (Formalism.WeaklyAdmissibleFiltrations.FilV (PDv bkP i v hv)) (GlobalTheory.DRFil.FilV_antitone _) (GlobalTheory.DRFil.exists_mem_FilV _)
    (GlobalTheory.DRFil.eq_zero_of_forall_mem_FilV _) M hM
  exact ⟨key.1, key.2 0⟩

end GlobalTheory.JumpDims
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankDdRAndFilZeroOfJumpMultisetStatement

section

@[expose] public section

open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

theorem _root_.GlobalTheory.T.finrank_DdR_and_fil_zero_of_jump_multiset : ∀ (D : D7) (bkP : BlochKatoReduction.BK D) (i : D.ntw.Tw) (s : D.ntw.Sig i), ∀ (v : HeightOneSpectrum (𝓞 D.host.E)) (hv : v ∈ placesOver D.host.E (D.ntw.l i)) (τ : EmbV bkP i v hv) (M : Multiset ℤ), HodgeL bkP i s → (∀ a : ℤ, Formalism.WeaklyAdmissibleFiltrations.multV (PDv bkP i v hv) (repV bkP i v hv (Tgl i s)) τ a = (M.count a : ℤ)) → dimD bkP i v hv (Tgl i s) τ = Multiset.card M ∧ dimFil0 bkP i v hv (Tgl i s) τ = Multiset.card (M.filter (0 ≤ ·)) := by
  first | exact @GlobalTheory.JumpDims.dims_of_mult | exact GlobalTheory.JumpDims.dims_of_mult | (intros; apply GlobalTheory.JumpDims.dims_of_mult <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugateNegativeJumpCountOfGoodHodgeJumps

section

@[expose] public section

open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.TripleGal

theorem card_filter_nonneg_add_reflect (t : ℤ) (ht : 0 ≤ t) (M : Multiset ℤ) (h : ∀ a ∈ M, a < -1 ∨ t < a) :
    Multiset.card (M.filter (0 ≤ ·)) + Multiset.card ((M.map (fun a => t - 1 - a)).filter (0 ≤ ·)) =
      Multiset.card M := by
  rw [Multiset.filter_map, Multiset.card_map]
  have e : M.filter ((fun a => 0 ≤ a) ∘ fun a => t - 1 - a) = M.filter (fun a => ¬ 0 ≤ a) := by
    apply Multiset.filter_congr
    intro a ha
    have := h a ha
    simp only [Function.comp_apply]
    omega
  rw [e, ← Multiset.card_add, Multiset.filter_add_not]

theorem negCount_of_goodJ : ∀ (D : D7) (bkP : BlochKatoReduction.BK D) (i : D.ntw.Tw) (s : D.ntw.Sig i), ∀ (ι : FractionRing (D.ntw.O0 i) →+* ℂ) (J : (D.host.E →+* ℂ) → Multiset ℤ), HodgeL bkP i s → JumpsAre bkP i s ι J → GoodJ D J → NegCount bkP i s := by
  intro D bkP i s ι J hH hJ hG v v' hv hv' τ τ' hc
  obtain ⟨τc, h1, h2⟩ := GlobalTheory.T.exists_complex_reading_local_embedding D bkP i ι v hv τ
  have h2' := h2 v' hv' τ' hc
  obtain ⟨a1, a2⟩ := GlobalTheory.T.finrank_DdR_and_fil_zero_of_jump_multiset D bkP i s v hv τ (J τc) hH (hJ v hv τ τc h1)
  obtain ⟨b1, b2⟩ := GlobalTheory.T.finrank_DdR_and_fil_zero_of_jump_multiset D bkP i s v' hv' τ' (J (τc.comp (cj D))) hH (hJ v' hv' τ' _ h2')
  obtain ⟨g1, g2, g3⟩ := hG τc
  have k := card_filter_nonneg_add_reflect (D.R.t : ℤ) (by positivity) (J τc) g3
  rw [a1, a2, b1, b2, g2, Multiset.card_map]
  omega

end GlobalTheory.TripleGal
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugateNegativeJumpCountOfGoodHodgeJumpsStatement

section

@[expose] public section

open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

theorem _root_.GlobalTheory.T.conjugateNegativeJumpCount_of_goodHodgeJumps : ∀ (D : D7) (bkP : BlochKatoReduction.BK D) (i : D.ntw.Tw) (s : D.ntw.Sig i), ∀ (ι : FractionRing (D.ntw.O0 i) →+* ℂ) (J : (D.host.E →+* ℂ) → Multiset ℤ), HodgeL bkP i s → JumpsAre bkP i s ι J → GoodJ D J → NegCount bkP i s := by
  first | exact @GlobalTheory.TripleGal.negCount_of_goodJ | exact GlobalTheory.TripleGal.negCount_of_goodJ | (intros; apply GlobalTheory.TripleGal.negCount_of_goodJ <;> assumption)
end
end
