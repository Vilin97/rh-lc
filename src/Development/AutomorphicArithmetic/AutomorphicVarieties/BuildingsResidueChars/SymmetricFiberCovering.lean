module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.FibAbs
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.OrbitalFiberOfBot
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.OrbitalFiberPushforward
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.OrbitalFiberCardFormula

section

@[expose] public section

theorem UpperTheory.orbitalFiber_card_formula : UpperTheory.V.Z.Sym.Glob.Fib.CardFib := by
  intro G _ S U U' x Ux s₀ hS hU hx
  classical
  have hmem : ∀ w : ↥(U' ⊓ S), (s₀ : G) * x * (w : G) * x⁻¹ ∈ S := by
    intro w
    have h1 := S.mul_mem s₀.2 (hS.conj_mem (w : G) (Subgroup.mem_inf.1 w.2).2 x)
    simpa [mul_assoc] using h1
  let g : ↥(U' ⊓ S) → ↥S ⧸ Ux := fun w => ((⟨_, hmem w⟩ : ↥S) : ↥S ⧸ Ux)
  have hg : ∀ w w' : ↥(U' ⊓ S), g w = g w' ↔ (w : G)⁻¹ * (w' : G) ∈ U := by
    intro w w'
    simp only [g]
    rw [QuotientGroup.eq, hx]
    have e : x⁻¹ * (((⟨_, hmem w⟩ : ↥S)⁻¹ * ⟨_, hmem w'⟩ : ↥S) : G) * x = (w : G)⁻¹ * (w' : G) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [e]
  have hgT : ∀ w, g w ∈ {s : ↥S ⧸ Ux | (((Quotient.out s : ↥S) : G) * x : G ⧸ U') = ((s₀ : G) * x : G ⧸ U')} := by
    intro w
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul Ux (⟨_, hmem w⟩ : ↥S)
    simp only [Set.mem_setOf_eq, g]
    rw [hk, QuotientGroup.eq]
    have hkU : x⁻¹ * ((k : ↥S) : G) * x ∈ U' := hU ((hx k).1 k.2)
    have e : ((((⟨_, hmem w⟩ : ↥S) * (k : ↥S) : ↥S) : G) * x)⁻¹ * ((s₀ : G) * x) =
        (x⁻¹ * ((k : ↥S) : G) * x)⁻¹ * ((w : G))⁻¹ := by
      simp only [Subgroup.coe_mul]
      group
    rw [e]
    exact U'.mul_mem (U'.inv_mem hkU) (U'.inv_mem (Subgroup.mem_inf.1 w.2).1)
  rw [← Nat.card_coe_set_eq]
  unfold Subgroup.relIndex Subgroup.index
  let F : ↥(U' ⊓ S) ⧸ U.subgroupOf (U' ⊓ S) →
      {s : ↥S ⧸ Ux | (((Quotient.out s : ↥S) : G) * x : G ⧸ U') = ((s₀ : G) * x : G ⧸ U')} :=
    Quotient.lift (fun w => ⟨g w, hgT w⟩) (fun a b hab => Subtype.ext ((hg a b).2 (by
      have h := QuotientGroup.leftRel_apply.1 hab
      simpa [Subgroup.mem_subgroupOf] using h)))
  refine (Nat.card_congr (Equiv.ofBijective F ⟨?_, ?_⟩)).symm
  · intro a b hab
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    have h := congrArg Subtype.val hab
    change g a = g b at h
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simpa using (hg a b).1 h
  · rintro ⟨s, hs⟩
    rw [Set.mem_setOf_eq] at hs
    have hwS : x⁻¹ * ((s₀ : G)⁻¹ * ((Quotient.out s : ↥S) : G)) * x ∈ S := by
      simpa using hS.conj_mem _ (S.mul_mem (S.inv_mem s₀.2) (Quotient.out s).2) x⁻¹
    have hwU : x⁻¹ * ((s₀ : G)⁻¹ * ((Quotient.out s : ↥S) : G)) * x ∈ U' := by
      have h1 := QuotientGroup.eq.1 hs
      have e : x⁻¹ * ((s₀ : G)⁻¹ * ((Quotient.out s : ↥S) : G)) * x =
          ((((Quotient.out s : ↥S) : G) * x)⁻¹ * ((s₀ : G) * x))⁻¹ := by
        group
      rw [e]
      exact U'.inv_mem h1
    refine ⟨((⟨_, Subgroup.mem_inf.2 ⟨hwU, hwS⟩⟩ : ↥(U' ⊓ S)) : ↥(U' ⊓ S) ⧸ U.subgroupOf (U' ⊓ S)),
      Subtype.ext ?_⟩
    change g _ = s
    conv_rhs => rw [← QuotientGroup.out_eq' s]
    simp only [g]
    congr 1
    apply Subtype.ext
    dsimp only
    group
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SymmetricFiberCovering

section

@[expose] public section

open MulAction

theorem UpperTheory.symmetric_fiber_covering : UpperTheory.V.Z.Sym.Glob.Fib.Cover := by
  intro H G _ _ S U U' x Ux ι Φ hS hU hUx hr hL hR hT hfin
  classical
  letI a1 : MulAction H (S ⧸ Ux) := MulAction.compHom _ ι
  letI a2 : MulAction H (G ⧸ U') := MulAction.compHom _ (S.subtype.comp ι)
  let q : S ⧸ Ux → G ⧸ U' := fun y => (((y.out : S) : G) * x : G)
  let k : S ⧸ Ux → ℂ := fun y => Φ (((y.out : S) : G) * x)
  have hΦ : ∀ a b : G, (a : G ⧸ U') = b → Φ a = Φ b := by
    intro a b e
    have hm : a⁻¹ * b ∈ U' := QuotientGroup.eq.1 e
    have := hR _ hm a
    rw [← this]
    congr 1
    group
  have hq0 : ∀ s : S, q (s : S ⧸ Ux) = (((s : G) * x : G) : G ⧸ U') := by
    intro s
    have h1 : ((s : S ⧸ Ux).out)⁻¹ * s ∈ Ux := QuotientGroup.eq.1 (QuotientGroup.out_eq' _)
    have h2 := hU ((hUx _).1 h1)
    show ((((s : S ⧸ Ux).out : G) * x : G) : G ⧸ U') = _
    rw [QuotientGroup.eq]
    have e : (((s : S ⧸ Ux).out : G) * x)⁻¹ * ((s : G) * x) = x⁻¹ * ((((s : S ⧸ Ux).out)⁻¹ * s : S) : G) * x := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [e]
    exact h2
  have hq : ∀ (h : H) (y : S ⧸ Ux), q (h • y) = h • q y := by
    intro h y
    induction y using QuotientGroup.induction_on with | H s => ?_
    have e1 : h • (s : S ⧸ Ux) = ((ι h * s : S) : S ⧸ Ux) := rfl
    rw [e1, hq0, hq0]
    have e2 : ∀ z : G ⧸ U', h • z = ((ι h : S) : G) • z := fun _ => rfl
    rw [e2, Subgroup.coe_mul, mul_assoc]
    rfl
  have hkq : ∀ y, k y = Φ (q y).out := fun y => hΦ _ _ (QuotientGroup.out_eq' (q y)).symm
  have hk : ∀ (h : H) y, k (h • y) = k y := by
    intro h y
    rw [hkq, hkq, hq]
    have e2 : h • q y = ((((ι h : S) : G) * (q y).out : G) : G ⧸ U') := by
      conv_lhs => rw [← QuotientGroup.out_eq' (q y)]
      rfl
    have := hΦ _ _ ((QuotientGroup.out_eq' (h • q y)).trans e2)
    rw [this]
    exact hL h _
  have hT' : ∃ T : Finset (S ⧸ Ux), ∀ y, k y ≠ 0 → ∃ h : H, ∃ s ∈ T, y = h • s := by
    obtain ⟨T, hT⟩ := hT
    refine ⟨T.image (fun t : S => (QuotientGroup.mk t : S ⧸ Ux)), fun y _ => ?_⟩
    induction y using QuotientGroup.induction_on with | H s => ?_
    obtain ⟨h, t, ht, u, hu, e⟩ := hT s
    refine ⟨h, (QuotientGroup.mk t : S ⧸ Ux), Finset.mem_image_of_mem (fun t : S => (QuotientGroup.mk t : S ⧸ Ux)) ht, ?_⟩
    rw [e]
    show ((ι h * t * u : S) : S ⧸ Ux) = ((ι h * t : S) : S ⧸ Ux)
    exact QuotientGroup.mk_mul_of_mem _ hu
  have hcard : ∀ s₀ : S, {y | q y = (((s₀ : G) * x : G) : G ⧸ U')}.ncard = U.relIndex (U' ⊓ S) :=
    fun s₀ => UpperTheory.orbitalFiber_card_formula G S U U' x Ux s₀ hS hU hUx
  have hfinF : ∀ s₀ : S, {y | q y = (((s₀ : G) * x : G) : G ⧸ U')}.Finite := fun s₀ =>
    Set.finite_of_ncard_ne_zero (by rw [hcard]; exact hr)
  have hfib : ∀ z, {y | q y = z ∧ k y ≠ 0}.Finite := by
    intro z
    by_cases hz : ∃ y, q y = z
    · obtain ⟨y, rfl⟩ := hz
      exact (hfinF y.out).subset fun w hw => hw.1
    · refine Set.Finite.subset Set.finite_empty fun w hw => hz ⟨w, hw.1⟩
  have hrel : ∀ y, k y ≠ 0 → (⊥ : Subgroup H).relIndex (stabilizer H (q y)) ≠ 0 := by
    intro y _
    rw [Subgroup.relIndex_bot_left]
    have hs : ((stabilizer H (q y) : Subgroup H) : Set H).Finite := by
      refine (hfin (q y).out).subset fun h hh => ?_
      have hh' : h • q y = q y := hh
      have e2 : h • q y = ((((ι h : S) : G) * (q y).out : G) : G ⧸ U') := by
        conv_lhs => rw [← QuotientGroup.out_eq' (q y)]
        rfl
      rw [e2] at hh'
      have e3 : (((q y).out : G) : G ⧸ U') = ((((ι h : S) : G) * (q y).out : G) : G ⧸ U') :=
        (QuotientGroup.out_eq' (q y)).trans hh'.symm
      have := QuotientGroup.eq.1 e3
      show ((q y).out)⁻¹ * ((ι h : S) : G) * (q y).out ∈ U'
      rwa [mul_assoc]
    haveI : Finite (stabilizer H (q y)) := hs.to_subtype
    exact Nat.card_pos.ne'
  have hpush := UpperTheory.orbitalFiber_pushforward H (S ⧸ Ux) (G ⧸ U') ⊥ q k inferInstance hq
    (fun z hz y => by rw [Subgroup.mem_bot.1 hz, one_smul]) hk hT' hfib hrel
  have hK : (fun z : G ⧸ U' => ∑ᶠ (y : S ⧸ Ux) (_ : q y = z), k y) =
      fun z => (U.relIndex (U' ⊓ S) : ℂ) * (orbit S (x : G ⧸ U')).indicator (fun y => Φ y.out) z := by
    funext z
    by_cases hz : z ∈ orbit S (x : G ⧸ U')
    · rw [Set.indicator_of_mem hz]
      obtain ⟨s₀, rfl⟩ := hz
      have e0 : (fun m : S => m • (x : G ⧸ U')) s₀ = (((s₀ : G) * x : G) : G ⧸ U') := rfl
      rw [e0]
      set z : G ⧸ U' := (((s₀ : G) * x : G) : G ⧸ U') with hzdef
      have step : (∑ᶠ (y : S ⧸ Ux) (_ : q y = z), k y) = ∑ᶠ y ∈ {y | q y = z}, Φ z.out :=
        by
          change (∑ᶠ y ∈ {y | q y = z}, k y) = ∑ᶠ y ∈ {y | q y = z}, Φ z.out
          exact finsum_mem_congr rfl fun y hy => by
            have hy' : q y = z := hy
            rw [hkq, hy']
      rw [step, finsum_mem_eq_finite_toFinset_sum _ (hfinF s₀), Finset.sum_const, nsmul_eq_mul,
        ← Set.ncard_eq_toFinset_card _ (hfinF s₀), hcard]
    · rw [Set.indicator_of_notMem hz, mul_zero]
      have h0 : ∀ y : S ⧸ Ux, (∑ᶠ (_ : q y = z), k y) = 0 := by
        intro y
        refine finsum_eq_if.trans (if_neg fun e => hz ?_)
        exact ⟨y.out, e⟩
      simp only [h0, finsum_zero]
  have hbot := (UpperTheory.orbitalFiber_of_bot H (G ⧸ U') ⊥ ((orbit S (x : G ⧸ U')).indicator fun y => Φ y.out)).1
    (U.relIndex (U' ⊓ S) : ℂ)
  show UpperTheory.V.Z.Sym.gq ⊥ k = (U.relIndex (U' ⊓ S) : ℂ) *
    UpperTheory.V.Z.Sym.gq ⊥ ((orbit S (x : G ⧸ U')).indicator fun y => Φ y.out)
  rw [hpush, hK]
  exact hbot
end
end
