module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFractionalIdealOfHermIdeleStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
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
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSplitPointFrameCharacterStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FractionalIdealHermitianSelfDualOfLocalGeneratorStatement
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotLineLatAtZero
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ValuationXiZeroEqOne

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIdeleChangeFinitelyManySplitPlaces

section

@[expose] public section

open NumberField
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel IsLocalRing GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.IdeleChange

open GlobalTheory.FinPl.FrameLat

variable {D : D7}

theorem idAt_le_idOff {x y : Pl D} (hxy : x ≠ y) : idAt D (· = x) ≤ idOff D (· = y) := by
  intro a ha
  unfold idOff
  rw [Submodule.mem_iInf]
  rintro ⟨w, rfl⟩
  exact (Submodule.mem_iInf _).1 (Submodule.mem_inf.1 ha).2 ⟨w, fun e => hxy e.symm⟩

theorem mul_eq_zero_of_ne {x y : Pl D} (hxy : x ≠ y) {a b : AE D} (ha : a ∈ idAt D (· = x))
    (hb : b ∈ idAt D (· = y)) : a * b = 0 := by
  obtain ⟨⟨ε, -, -, -, h1, h2⟩, -⟩ := GlobalTheory.FinPl.localComponents D (· = y)
  have hb' := (h1 b).1 hb
  have ha' := (h2 a).1 (idAt_le_idOff hxy ha)
  calc a * b = a * (ε * b) := by rw [hb']
    _ = (ε * a) * b := by ring
    _ = 0 := by rw [ha', zero_mul]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]



theorem exists_change_one (q : SplitPt D k) (h : D.host.E) (hh : h ≠ 0) (hs : star h = h) (m : (AE D)ˣ) :
    ∃ m' : (AE D)ˣ, (∀ x, x ≠ q.v → ∀ a ∈ idAt D (· = x),
        (m' : AE D) * a = (m : AE D) * a ∧ cA D (m' : AE D) * a = cA D (m : AE D) * a) ∧
      ∀ a ∈ idAt D (· = q.v), (m' : AE D) * cA D (m' : AE D) * incA D h * a = a := by
  have ht0 : q.pr (incA D h) ≠ 0 := by
    intro e
    exact hh ((map_eq_zero_iff (q.pr.comp (incA D)) (q.pr.comp (incA D)).injective).1 e)
  obtain ⟨t, ht⟩ : ∃ t : k, t = q.pr (incA D h) := ⟨_, rfl⟩
  rw [← ht] at ht0
  obtain ⟨s, hsdef⟩ : ∃ s : k, s = t⁻¹ := ⟨_, rfl⟩
  obtain ⟨f, hfdef⟩ : ∃ f : AE D, f = q.e + cA D q.e := ⟨_, rfl⟩
  have hf : ∀ b ∈ idAt D (· = q.v), f * b = b := fun b hb => by rw [hfdef]; exact (idem_iff q b).1 hb
  have hfm : f ∈ idAt D (· = q.v) := by rw [hfdef]; exact sum_mem_idAt q
  have hff : f * f = f := hf _ hfm
  have hcf : cA D f = f := by rw [hfdef, map_add (f := _), cA_cA, add_comm]
  have hec : q.e * cA D q.e = 0 := q.split.2.1
  have hce : cA D q.e * q.e = 0 := cAe_mul_e q
  have hcee : cA D q.e * cA D q.e = cA D q.e := by rw [← map_mul, q.split.1]
  have hsc : ∀ c, q.sec c * cA D q.e = 0 := fun c => by
    linear_combination (-(cA D q.e)) * e_mul_sec q c + q.sec c * hec
  have hcem : cA D q.e ∈ idAt D (· = q.v) := by rw [← sec_one]; exact csec_mem_idAt (p := q) 1
  obtain ⟨u, hudef⟩ : ∃ u : AE D, u = q.sec s + cA D q.e := ⟨_, rfl⟩
  obtain ⟨u', hu'def⟩ : ∃ u' : AE D, u' = q.sec t + cA D q.e := ⟨_, rfl⟩
  have hu : u ∈ idAt D (· = q.v) := by rw [hudef]; exact add_mem (sec_mem_idAt q _) hcem
  have hu' : u' ∈ idAt D (· = q.v) := by rw [hu'def]; exact add_mem (sec_mem_idAt q _) hcem
  have hcu : cA D u ∈ idAt D (· = q.v) := by
    rw [hudef, map_add (f := _), cA_cA]; exact add_mem (csec_mem_idAt (p := q) _) (e_mem_idAt q)
  have hst : q.sec s * q.sec t = q.e := by rw [← sec_mul, hsdef, inv_mul_cancel₀ ht0, sec_one]
  have huu : u * u' = f := by
    have h1 := hsc s
    have h2 : cA D q.e * q.sec t = 0 := by rw [mul_comm]; exact hsc t
    rw [hudef, hu'def, hfdef]
    linear_combination hst + h1 + h2 + hcee
  have hmm : (m : AE D) * ((m⁻¹ : (AE D)ˣ) : AE D) = 1 := m.mul_inv
  obtain ⟨mi, hmi⟩ : ∃ mi : AE D, mi = ((m⁻¹ : (AE D)ˣ) : AE D) := ⟨_, rfl⟩
  rw [← hmi] at hmm
  obtain ⟨w, hw⟩ : ∃ w : AE D, w = (m : AE D) * (1 - f) + u := ⟨_, rfl⟩
  obtain ⟨w', hw'⟩ : ∃ w' : AE D, w' = mi * (1 - f) + u' := ⟨_, rfl⟩
  have hww : w * w' = 1 := by
    rw [hw, hw']
    linear_combination (1 - f) ^ 2 * hmm + hff - (m : AE D) * hf _ hu' - mi * hf _ hu + huu
  have hcw : cA D w = cA D (m : AE D) * (1 - f) + cA D u := by
    rw [hw, map_add (f := _), map_mul, map_sub, map_one, hcf]
  refine ⟨Units.mkOfMulEqOne w w' hww, fun x hx a ha => ?_, fun a ha => ?_⟩
  · have hfa : f * a = 0 := mul_eq_zero_of_ne (Ne.symm hx) hfm ha
    have hua : u * a = 0 := mul_eq_zero_of_ne (Ne.symm hx) hu ha
    have hcua : cA D u * a = 0 := mul_eq_zero_of_ne (Ne.symm hx) hcu ha
    rw [Units.val_mkOfMulEqOne, hcw, hw]
    constructor
    · linear_combination (-(m : AE D)) * hfa + hua
    · linear_combination (-(cA D (m : AE D))) * hfa + hcua
  · rw [Units.val_mkOfMulEqOne]
    have hb : incA D h * a ∈ idAt D (· = q.v) := Ideal.mul_mem_left _ _ ha
    have hwa : ∀ b ∈ idAt D (· = q.v), w * b = u * b := fun b hb => by
      rw [hw]
      linear_combination (-(m : AE D)) * hf b hb
    have hcwa : ∀ b ∈ idAt D (· = q.v), cA D w * b = cA D u * b := fun b hb => by
      rw [hcw]
      linear_combination (-(cA D (m : AE D))) * hf b hb
    have hc2 : cA D u * (incA D h * a) ∈ idAt D (· = q.v) := Ideal.mul_mem_left _ _ hb
    have hA : q.sec s * incA D h = q.e := by
      rw [sec_mul_right, ← ht, hsdef, inv_mul_cancel₀ ht0, sec_one]
    have hB : cA D (q.sec s) * incA D h = cA D q.e := by
      have e0 : incA D h = cA D (incA D h) := by rw [cA_incA, hs]
      rw [e0, ← map_mul, hA]
    have hC1 : cA D q.e * cA D (q.sec s) = cA D (q.sec s) := by rw [← map_mul, e_mul_sec]
    have hD : q.sec s * q.e = q.sec s := by rw [mul_comm, e_mul_sec]
    have hkey : u * cA D u * incA D h = f := by
      rw [hudef, hfdef, map_add (f := _), cA_cA]
      linear_combination (incA D h) * ((-(q.sec s)) * hC1 + (cA D (q.sec s)) * hsc s + hD + hce + hC1) + hA + hB
    calc w * cA D w * incA D h * a = w * (cA D w * (incA D h * a)) := by ring
      _ = u * (cA D u * (incA D h * a)) := by rw [hcwa _ hb, hwa _ hc2]
      _ = (u * cA D u * incA D h) * a := by ring
      _ = a := by rw [hkey, hf a ha]

theorem exists_change_list {ι : Type} (p : ι → SplitPt D k) (hp : Function.Injective fun i => (p i).v) (h : D.host.E)
    (hh : h ≠ 0) (hs : star h = h) (m : (AE D)ˣ) (l : List ι) :
    ∃ m' : (AE D)ˣ, (∀ x, (∀ i ∈ l, x ≠ (p i).v) → ∀ a ∈ idAt D (· = x),
        (m' : AE D) * a = (m : AE D) * a ∧ cA D (m' : AE D) * a = cA D (m : AE D) * a) ∧
      ∀ i ∈ l, ∀ a ∈ idAt D (· = (p i).v), (m' : AE D) * cA D (m' : AE D) * incA D h * a = a := by
  induction l with
  | nil => exact ⟨m, fun _ _ _ _ => ⟨rfl, rfl⟩, fun _ hi => absurd hi List.not_mem_nil⟩
  | cons i l ih =>
    obtain ⟨m₁, hA₁, hB₁⟩ := ih
    obtain ⟨m₂, hA₂, hB₂⟩ := exists_change_one (p i) h hh hs m₁
    refine ⟨m₂, fun x hx a ha => ?_, fun j hj a ha => ?_⟩
    · have e2 := hA₂ x (hx i List.mem_cons_self) a ha
      have e1 := hA₁ x (fun j hj => hx j (List.mem_cons_of_mem _ hj)) a ha
      exact ⟨e2.1.trans e1.1, e2.2.trans e1.2⟩
    · by_cases e : j = i
      · subst e; exact hB₂ a ha
      · have hj' : j ∈ l := (List.mem_cons.1 hj).resolve_left e
        have hne : (p j).v ≠ (p i).v := fun e' => e (hp e')
        have hb : incA D h * a ∈ idAt D (· = (p j).v) := Ideal.mul_mem_left _ _ ha
        have e1 := (hA₂ _ hne _ hb).2
        have hc : cA D (m₁ : AE D) * (incA D h * a) ∈ idAt D (· = (p j).v) := Ideal.mul_mem_left _ _ hb
        have e2 := (hA₂ _ hne _ hc).1
        calc (m₂ : AE D) * cA D (m₂ : AE D) * incA D h * a = (m₂ : AE D) * (cA D (m₂ : AE D) * (incA D h * a)) := by ring
          _ = (m₁ : AE D) * (cA D (m₁ : AE D) * (incA D h * a)) := by rw [e1, e2]
          _ = (m₁ : AE D) * cA D (m₁ : AE D) * incA D h * a := by ring
          _ = a := hB₁ j hj' a ha

end GlobalTheory.FinPl.IdeleChange


open GlobalTheory.FinPl.IdeleChange in
theorem GlobalTheory.FinPl.exists_idele_change_split : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (I : List ι) (P : Pl D → Prop), Places p I P → ∀ h : D.host.E, h ≠ 0 → star h = h → ∀ m : (AE D)ˣ, ∃ m' : (AE D)ˣ, (∀ x, ¬ P x → ∀ a ∈ idAt D (· = x), (m' : AE D) * a = (m : AE D) * a ∧ cA D (m' : AE D) * a = cA D (m : AE D) * a) ∧ ∀ x, P x → ∀ a ∈ idAt D (· = x), a ∈ intAt D (· = x) ↔ (m' : AE D) * cA D (m' : AE D) * incA D h * a ∈ intAt D (· = x) := by
  intro D k _ _ _ _ ι p I P hP h hh hs m
  obtain ⟨m', hA, hB⟩ := exists_change_list p hP.inj h hh hs m I
  refine ⟨m', fun x hx a ha => hA x (fun i _ e => hx ((hP.mem x).2 ⟨i, e⟩)) a ha, fun x hx a ha => ?_⟩
  obtain ⟨i, rfl⟩ := (hP.mem x).1 hx
  rw [hB i (hP.all i) a ha]
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIdeleChangeFinitelyManySplitPlacesStatement

section

@[expose] public section

open NumberField
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel IsLocalRing GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_idele_change_finitely_many_split_places : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (I : List ι) (P : Pl D → Prop), Places p I P → ∀ h : D.host.E, h ≠ 0 → star h = h → ∀ m : (AE D)ˣ, ∃ m' : (AE D)ˣ, (∀ x, ¬ P x → ∀ a ∈ idAt D (· = x), (m' : AE D) * a = (m : AE D) * a ∧ cA D (m' : AE D) * a = cA D (m : AE D) * a) ∧ ∀ x, P x → ∀ a ∈ idAt D (· = x), a ∈ intAt D (· = x) ↔ (m' : AE D) * cA D (m' : AE D) * incA D h * a ∈ intAt D (· = x) := by
  first | exact @GlobalTheory.FinPl.exists_idele_change_split | exact GlobalTheory.FinPl.exists_idele_change_split | (intros; apply GlobalTheory.FinPl.exists_idele_change_split <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LineLatticeSelfDual

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw.LiftModel

theorem isSelfDualC_lineLat : ∀ (D : D7) (S : HSp D) (ζ : Fin S.rank → D.host.E), IsLineVec S ζ → ∀ (𝔄 : FI D), (∀ d : D.host.E, d ∈ 𝔄 ↔ ∀ c ∈ 𝔄, ∃ b : 𝓞 D.host.E, (b : D.host.E) = star c * d * (star ζ ⬝ᵥ S.gram *ᵥ ζ)) → IsSelfDualC S (GlobalTheory.SeeSaw.LiftModel.lineLat S ζ 𝔄) := by
  intro D S ζ hζ 𝔄 h𝔄
  classical
  obtain ⟨h1, hH⟩ := hζ
  haveI : Subsingleton (Fin S.rank) := by rw [h1]; infer_instance
  let i₀ : Fin S.rank := ⟨0, by omega⟩
  have all : ∀ i : Fin S.rank, i = i₀ := fun i => Subsingleton.elim _ _
  set z := ζ i₀ with hz
  set g := S.gram i₀ i₀ with hg
  have eH : star ζ ⬝ᵥ S.gram *ᵥ ζ = star z * (g * z) := by
    simp only [dotProduct, mulVec, Fintype.sum_subsingleton _ i₀, Pi.star_apply]
    rfl
  have z0 : z ≠ 0 := by
    intro h0; apply hH; rw [eH, h0]; simp
  have repr : ∀ y : Fin S.rank → D.host.E, y = (y i₀ / z) • ζ := by
    intro y; funext i; rw [all i]; simp [div_mul_cancel₀ _ z0, ← hz]
  have memΛ : ∀ y, y ∈ lineLat S ζ 𝔄 ↔ ∃ c ∈ 𝔄, c • ζ = y := by
    intro y
    simp [lineLat, Submodule.mem_map, LinearMap.toSpanSingleton_apply]
  have memΛ' : ∀ y, y ∈ lineLat S ζ 𝔄 ↔ y i₀ / z ∈ 𝔄 := by
    intro y
    rw [memΛ]
    constructor
    · rintro ⟨c, hc, rfl⟩
      simpa [← hz, mul_div_cancel_right₀ _ z0] using hc
    · intro h
      exact ⟨_, h, (repr y).symm⟩
  have sum_eq : ∀ c d : D.host.E, ∑ i, ∑ j, star ((c • ζ) i) * S.gram i j * (d • ζ) j =
      star c * d * (star ζ ⬝ᵥ S.gram *ᵥ ζ) := by
    intro c d
    rw [eH]
    simp only [Fintype.sum_subsingleton _ i₀, Pi.smul_apply, smul_eq_mul, star_mul', ← hz, ← hg]
    ring
  have dual : ∀ y : Fin S.rank → D.host.E, y ∈ lineLat S ζ 𝔄 ↔
      ∀ x ∈ lineLat S ζ 𝔄, ∃ b : 𝓞 D.host.E, (b : D.host.E) = ∑ i, ∑ j, star (x i) * S.gram i j * y j := by
    intro y
    rw [memΛ', h𝔄]
    constructor
    · intro h x hx
      obtain ⟨c, hc, rfl⟩ := (memΛ x).1 hx
      obtain ⟨b, hb⟩ := h c hc
      refine ⟨b, ?_⟩
      conv_rhs => rw [repr y]
      rw [sum_eq, hb]
    · intro h c hc
      obtain ⟨b, hb⟩ := h (c • ζ) ((memΛ _).2 ⟨c, hc, rfl⟩)
      refine ⟨b, ?_⟩
      rw [hb]
      conv_lhs => rw [repr y]
      rw [sum_eq]
  refine ⟨⟨?_, ?_⟩, dual⟩
  · exact (FractionalIdeal.fg_of_isNoetherianRing le_rfl 𝔄).map _
  · obtain ⟨c, hc, hc0⟩ : ∃ c ∈ 𝔄, c ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      have h1m : (1 : D.host.E) ∈ 𝔄 := by
        rw [h𝔄]
        intro c hc
        exact ⟨0, by simp [hcon c hc]⟩
      exact one_ne_zero (hcon 1 h1m)
    have hcζ : c • ζ ∈ lineLat S ζ 𝔄 := (memΛ _).2 ⟨c, hc, rfl⟩
    intro s hs hli
    exact (LinearIndependent.iff_fractionRing _ _).mp hli
end GlobalTheory.SeeSaw.LiftModel
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSumFrame

section

@[expose] public section

open NumberField
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel IsLocalRing GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.FinPl.CoreIdele

variable {D : D7}

theorem card_eq_of_inv {k : Type} [Field k] {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (b : Matrix m n k) (b' : Matrix n m k) (h : b * b' = 1) (h' : b' * b = 1) : Fintype.card n = Fintype.card m := by
  have h1 : Fintype.card m ≤ Fintype.card n := by
    have := Matrix.rank_mul_le_left b b'
    rw [h, Matrix.rank_one] at this
    exact this.trans (Matrix.rank_le_card_width b)
  have h2 : Fintype.card n ≤ Fintype.card m := by
    have := Matrix.rank_mul_le_left b' b
    rw [h', Matrix.rank_one] at this
    exact this.trans (Matrix.rank_le_card_width b')
  omega

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_sumFrame' (p : SplitPt D k) {S A L : HSp D} (o : OrthDec S A L) {ζ : Fin L.rank → D.host.E}
    (hζ : IsLineVec L ζ) {n : Type} [Fintype n] [DecidableEq n] (β : Frame p A n) :
    ∃ β₀ : Frame p S (n ⊕ Fin 1), IsSumFrame o ζ β β₀ := by
  let f : D.host.E →+* k := p.pr.comp (incA D)
  let r : Fin L.rank → D.host.E := (star ζ ⬝ᵥ L.gram *ᵥ ζ)⁻¹ • (star ζ ᵥ* L.gram)
  have hr : r ⬝ᵥ ζ = 1 := by
    simp only [r]
    rw [smul_dotProduct, ← dotProduct_mulVec, smul_eq_mul, inv_mul_cancel₀ hζ.2]
  let bE : Matrix (Fin S.rank) (Fin A.rank ⊕ Fin 1) D.host.E := fromCols o.iA (replicateCol (Fin 1) (o.iB *ᵥ ζ))
  let bE' : Matrix (Fin A.rank ⊕ Fin 1) (Fin S.rank) D.host.E := fromRows o.qA (replicateRow (Fin 1) (r ᵥ* o.qB))
  have h1 : bE' * bE = 1 := by
    simp only [bE, bE']
    rw [fromRows_mul_fromCols, ← Matrix.fromBlocks_one]
    congr 1
    · exact o.qA_iA
    · rw [← replicateCol_mulVec, Matrix.mulVec_mulVec, o.qA_iB, Matrix.zero_mulVec]; rfl
    · rw [← replicateRow_vecMul, Matrix.vecMul_vecMul, show o.qB * o.iA = 0 from o.symm.qA_iB, Matrix.vecMul_zero]; rfl
    · ext i j
      rw [replicateRow_mul_replicateCol_apply, dotProduct_mulVec, Matrix.vecMul_vecMul,
        show o.qB * o.iB = 1 from o.symm.qA_iA, Matrix.vecMul_one, hr, Subsingleton.elim i j, Matrix.one_apply_eq]
  have hn : Fintype.card n = A.rank := by simpa using card_eq_of_inv β.b β.b' β.bb' β.b'b
  let X : Matrix (Fin A.rank ⊕ Fin 1) (n ⊕ Fin 1) k := fromBlocks β.b 0 0 1
  let X' : Matrix (n ⊕ Fin 1) (Fin A.rank ⊕ Fin 1) k := fromBlocks β.b' 0 0 1
  have hX : X' * X = 1 := by
    simp only [X, X', fromBlocks_multiply, β.b'b]; simp
  have g1 : (X' * bE'.map f) * (bE.map f * X) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (bE'.map f), ← Matrix.map_mul, h1, Matrix.map_one _ (map_zero f) (map_one f),
      Matrix.one_mul, hX]
  have hc : Fintype.card (Fin S.rank) = Fintype.card (n ⊕ Fin 1) := by
    have := o.rank_add; have := hζ.1
    simp only [Fintype.card_fin, Fintype.card_sum, hn]; omega
  have g2 : (bE.map f * X) * (X' * bE'.map f) = 1 := (Matrix.mul_eq_one_comm_of_equiv (Fintype.equivOfCardEq hc)).2 g1
  obtain ⟨β₀, h₀⟩ := ((GlobalTheory.T.exists_splitPoint_frame_character D).2 k p).1 S (n ⊕ Fin 1) _ _ g2 g1
  refine ⟨β₀, ?_⟩
  rw [IsSumFrame, h₀]
  simp only [bE, X, fromCols_map, fromCols_mul_fromBlocks, Matrix.mul_zero, add_zero, zero_add, Matrix.mul_one]
  ext i (j | j) <;> rfl

theorem line_of_orth {S A L : HSp D} (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) (M : Lat S) (LA : Lat A) (LL : Lat L)
    (v : Pl D) (ho : OrthAt o M LA LL v) (a : AE D) :
    a • ratV (vecB o ζ) ∈ latV S M (· = v) ↔ a • ratV ζ ∈ latV L LL (· = v) := by
  have e : ratV (vecB o ζ) = o.jB *ᵥ ratV ζ := by
    funext i
    simp [ratV, vecB, OrthDec.jB, rat, mulVec, dotProduct]
  rw [ho, e, mulVec_smul, mulVec_smul, mulVec_mulVec, mulVec_mulVec, o.pA_jB, o.pB_jB, zero_mulVec, smul_zero, one_mulVec]
  exact and_iff_right (zero_mem _)

end GlobalTheory.FinPl.CoreIdele

theorem GlobalTheory.FinPl.CoreIdele.lineLat_idele : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (I : List ι) (P : Pl D → Prop), Places p I P → ∀ (L : HSp D) (ζ : Fin L.rank → D.host.E), IsLineVec L ζ → ∀ m : (AE D)ˣ, (∀ x, ¬ P x → ∀ a ∈ idAt D (· = x), a ∈ intAt D (· = x) ↔ (m : AE D) * cA D (m : AE D) * incA D (star ζ ⬝ᵥ L.gram *ᵥ ζ) * a ∈ intAt D (· = x)) → ∃ LL : Lat L, IsSelfDualC L LL ∧ ∀ x, ¬ P x → ∀ a ∈ idAt D (· = x), a • ratV ζ ∈ latV L LL (· = x) ↔ ((m⁻¹ : (AE D)ˣ) : AE D) * a ∈ intAt D (· = x) := by
  intro D k _ _ _ _ ι p I P hP L ζ hζ m hm
  set h := star ζ ⬝ᵥ L.gram *ᵥ ζ with hhdef
  have hh : star h = h := by
    have hG : ∀ i j, star (L.gram i j) = L.gram j i := fun i j => by
      have := congrFun (congrFun (gram_conjTranspose L) j) i
      simpa [Matrix.conjTranspose_apply] using this
    have e : star (star ζ ⬝ᵥ L.gram *ᵥ ζ) = star ζ ⬝ᵥ L.gram *ᵥ ζ := by
      simp only [dotProduct, mulVec, Pi.star_apply, star_sum, star_mul', star_star, Finset.mul_sum, hG]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    exact e
  obtain ⟨m', hoff, hon⟩ := GlobalTheory.T.exists_idele_change_finitely_many_split_places D k ι p I P hP h hζ.2 hh m
  obtain ⟨𝔞, h𝔞⟩ := GlobalTheory.T.exists_fractionalIdeal_of_hermIdele D m'
  have key : ∀ x, ¬ P x → ∀ a ∈ idAt D (· = x), ((m'⁻¹ : (AE D)ˣ) : AE D) * a = ((m⁻¹ : (AE D)ˣ) : AE D) * a := by
    intro x hx a ha
    have h1 : ((m⁻¹ : (AE D)ˣ) : AE D) * a ∈ idAt D (· = x) := Ideal.mul_mem_left _ _ ha
    have h2 := (hoff x hx _ h1).1
    rw [← mul_assoc (m : AE D), Units.mul_inv, one_mul] at h2
    calc ((m'⁻¹ : (AE D)ˣ) : AE D) * a = ((m'⁻¹ : (AE D)ˣ) : AE D) * ((m' : AE D) * (((m⁻¹ : (AE D)ˣ) : AE D) * a)) := by
          rw [h2]
      _ = ((m⁻¹ : (AE D)ˣ) : AE D) * a := by rw [← mul_assoc, Units.inv_mul, one_mul]
  have hloc : ∀ x : Pl D, ∀ a ∈ idAt D (· = x), a ∈ intAt D (· = x) ↔
      (m' : AE D) * cA D (m' : AE D) * incA D h * a ∈ intAt D (· = x) := by
    intro x a ha
    by_cases hx : P x
    · exact hon x hx a ha
    · have h1 : incA D h * a ∈ idAt D (· = x) := Ideal.mul_mem_left _ _ ha
      have h2 : cA D (m : AE D) * (incA D h * a) ∈ idAt D (· = x) := Ideal.mul_mem_left _ _ h1
      have e : (m' : AE D) * cA D (m' : AE D) * incA D h * a = (m : AE D) * cA D (m : AE D) * incA D h * a := by
        rw [mul_assoc, mul_assoc, (hoff x hx _ h1).2, (hoff x hx _ h2).1, ← mul_assoc, ← mul_assoc]
      rw [e]
      exact hm x hx a ha
  have hsd := GlobalTheory.T.fractionalIdeal_hermitianSelfDual_of_local_generators D h 𝔞 m' h𝔞 hloc
  have hζ0 : ζ ≠ 0 := fun e => hζ.2 (by rw [e]; simp)
  refine ⟨GlobalTheory.SeeSaw.LiftModel.lineLat L ζ 𝔞, GlobalTheory.SeeSaw.LiftModel.isSelfDualC_lineLat D L ζ hζ 𝔞 hsd, fun x hx a ha => ?_⟩
  rw [GlobalTheory.SeeSaw.LiftModel.lineLatAt_lineLat L hζ0 𝔞 x a ha, h𝔞 x a ha, key x hx a ha]


open GlobalTheory.FinPl.CoreIdele GlobalTheory.SeeSaw.CoreGlue in
theorem GlobalTheory.FinPl.CoreIdele.exists_core : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (I : List ι) (P : Pl D → Prop), Places p I P → ∀ (q : Unif k) (n : Type) [Fintype n] [DecidableEq n] (ρ : ℕ) (B : BesLev D ρ) (β : ∀ i, Frame (p i) B.A n) (Q : ι → Pair k n) (LA : Lat B.A), IsSelfDualC B.A LA → (∀ i, (β i).IsLat LA (Q i).lat) → (∀ i, valuation k ((p i).pr (incA D (star B.ζ ⬝ᵥ B.L.gram *ᵥ B.ζ))) = valuation k ((q.1 : 𝒪[k]) : k)) → ∀ m : (AE D)ˣ, (∀ x, P x → ∀ a ∈ idAt D (· = x), a ∈ intAt D (· = x) ↔ (m : AE D) * a ∈ intAt D (· = x)) → (∀ x, ¬ P x → ∀ a ∈ idAt D (· = x), a ∈ intAt D (· = x) ↔ (m : AE D) * cA D (m : AE D) * incA D (star B.ζ ⬝ᵥ B.L.gram *ᵥ B.ζ) * a ∈ intAt D (· = x)) → ∃ (M : Lat B.V₀) (β₀ : ∀ i, Frame (p i) B.V₀ (n ⊕ Fin 1)), IsSelfDualC B.V₀ M ∧ (∀ i, GluedCore B M q (β i) (β₀ i) (Q i)) ∧ (∀ x, ¬ P x → ∃ LL : Lat B.L, IsSelfDualC B.L LL ∧ OrthAt B.o M LA LL x ∧ ∀ a ∈ idAt D (· = x), a • ratV B.ζ ∈ latV B.L LL (· = x) ↔ ((m⁻¹ : (AE D)ˣ) : AE D) * a ∈ intAt D (· = x)) ∧ ∀ x, ∀ a ∈ idAt D (· = x), a • ratV (vecB B.o B.ζ) ∈ latV B.V₀ M (· = x) ↔ ((m⁻¹ : (AE D)ˣ) : AE D) * a ∈ intAt D (· = x) := by
  intro D k _ _ _ _ ι p I P hP q n _ _ ρ B β Q LA hLA _ hnorm m hmP hmoff
  obtain ⟨LL, hLL, hline⟩ := lineLat_idele D k ι p I P hP B.L B.ζ B.line m hmoff
  obtain ⟨M₁, hM₁, horth⟩ := exists_orthSum B.o hLA hLL
  have frames : ∀ i, ∃ β₀ : Frame (p i) B.V₀ (n ⊕ Fin 1), IsSumFrame B.o B.ζ (β i) β₀ :=
    fun i => exists_sumFrame' (p i) B.o B.line (β i)
  choose β₀ hβ₀ using frames
  obtain ⟨M, hM, hlat, hoff⟩ := exists_modify hP.inj β₀ (fun i => gluedS q 1 (Q i).ker (Q i).vec)
    (fun i => by haveI := (Q i).ker_isLat; infer_instance) hM₁ I
  have glued : ∀ i, GluedCore B M q (β i) (β₀ i) (Q i) := fun i =>
    ⟨hP.unit i, hβ₀ i, hnorm i, hlat i (hP.all i)⟩
  have offP : ∀ x, ¬ P x → ∀ i, x ≠ (p i).v := fun x hx i e => hx ((hP.mem x).2 ⟨i, e⟩)
  have horthM : ∀ x, ¬ P x → OrthAt B.o M LA LL x := fun x hx y => by
    rw [hoff x (offP x hx)]
    exact horth x y
  refine ⟨M, β₀, hM, glued, fun x hx => ⟨LL, hLL, horthM x hx, hline x hx⟩, fun x a ha => ?_⟩
  by_cases hx : P x
  · obtain ⟨i, rfl⟩ := (hP.mem x).1 hx
    rw [line_of_glued hM (glued i) ha]
    have hma : ((m⁻¹ : (AE D)ˣ) : AE D) * a ∈ idAt D (· = (p i).v) := Ideal.mul_mem_left _ _ ha
    have := hmP _ hx _ hma
    rw [← mul_assoc, Units.mul_inv, one_mul] at this
    exact this.symm
  · rw [line_of_orth B.o B.ζ M LA LL x (horthM x hx) a]
    exact hline x hx a ha
end
end
end
