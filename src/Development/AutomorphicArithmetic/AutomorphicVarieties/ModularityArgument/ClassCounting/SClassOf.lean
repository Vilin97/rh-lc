module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LemmaKOfSteps
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LatticeBlockClasses.BlkEquiv
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LatticeBlockClasses.CBetaDiv
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LatticeBlockClasses.CBetaVal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LatticeBlockClasses.CBlockValAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SChain
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SPrism
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SPrismMul
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LatticeBlockClasses.CBlock
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LatticeBlockClasses.MemPowEqv
import Mathlib.Tactic.Basify
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LatticeBlockClasses.CJoin
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LatticeBlockClasses.CLatLoc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LatticeBlockClasses.CMu
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LatticeBlockClasses.CSplit
import Mathlib.Tactic.ENatToNat
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LatticeBlockClasses.CRes
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LatticeBlockClasses.MemPowEqv
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LatticeBlockClasses.ExistsOfInLat
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LatticeBlockClasses.GtEqZeta
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LatticeBlockClasses.InLat
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LatticeBlockClasses.RedApplyMap

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LatticeBlockClasses.CChain

section

@[expose] public section

open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.KL UpperTheory.V.ZK UpperTheory.V.ZK.Cl

theorem UpperTheory.V.ZK.Cl.cChain :
    UpperTheory.V.ZK.Cl.CChain := by
  unfold UpperTheory.V.ZK.Cl.CChain
  intro A _ C D G _ _ _ ι _ m H ρ d n z g t₀ hz hB hc hρ hσ hg
  obtain ⟨-, h1, h2, h3, -⟩ := sChain A
  have hz' : bd A C m z = 0 := hz
  have hcyc : ∀ (K : Type) [Group K] (f : C →* K), bd A K m (cm A f (m + 1) z) = 0 := by
    intro K _ f
    rw [h1, hz', map_zero]
  let ρH : D →* H := ρ.codRestrict H hρ
  have hσ' : ∀ x, (MulAut.conj (g t₀)⁻¹).toMonoidHom.comp ρ x ∈ H := by
    intro x
    simpa using hσ x
  let σH : D →* H := ((MulAut.conj (g t₀)⁻¹).toMonoidHom.comp ρ).codRestrict H hσ'
  let k : ι → H := fun t => (⟨(g t)⁻¹ * g t₀, hg t⟩ : H)⁻¹
  obtain ⟨b, hb⟩ := LinearMap.mem_range.mp hB
  have hconj : ∀ t, (MulAut.conj (k t)⁻¹).toMonoidHom.comp (σH.comp (d t)) = ρH.comp (d t) := by
    intro t
    ext c
    have e := (hc t c).eq
    simp [σH, ρH, k]
    calc _ = (g t)⁻¹ * (ρ (d t c) * g t) := by group
      _ = ρ (d t c) := by rw [← e]; group
  refine ⟨cm A σH (m + 2) b - cm A ρH (m + 2) b + ∑ t, n t • prism A (k t) (m + 1) (cm A (σH.comp (d t)) (m + 1) z), ?_, ?_⟩
  · show bd A H (m + 1) _ = 0
    have hp : ∀ t, bd A H (m + 1) (prism A (k t) (m + 1) (cm A (σH.comp (d t)) (m + 1) z)) = cm A (ρH.comp (d t)) (m + 1) z - cm A (σH.comp (d t)) (m + 1) z := by
      intro t
      have e := sPrism A H (k t) m (cm A (σH.comp (d t)) (m + 1) z)
      rw [hcyc, map_zero, add_zero, ← h2] at e
      rw [e, hconj t]

    rw [map_add (f := _), map_sub, map_sum, h1, h1, hb]

    simp only [map_smul, hp, map_sum, ← h2, smul_sub, Finset.sum_sub_distrib]
    abel
  · have hk : ∀ t, H.subtype (k t) = (g t₀)⁻¹ * g t := by
      intro t
      simp [k]
    have hincl1 : H.subtype.comp σH = (MulAut.conj (g t₀)⁻¹).toMonoidHom.comp ρ := by
      ext x
      rfl
    have hincl2 : H.subtype.comp ρH = ρ := by
      ext x
      rfl
    have hincl3 : ∀ t, H.subtype.comp (σH.comp (d t)) = (MulAut.conj (g t₀)⁻¹).toMonoidHom.comp (ρ.comp (d t)) := by
      intro t
      ext x
      rfl
    have hx : ∀ t, Cyc (cm A (ρ.comp (d t)) (m + 1) z) := fun t => hcyc G _
    choose e he using fun t => LinearMap.mem_range.mp (sPrismMul A G (g t₀) ((g t₀)⁻¹ * g t) m _ (hx t))
    have hS := sPrism A G (g t₀) (m + 1) (cm A ρ (m + 2) b)
    rw [h1, hb, ← h2] at hS
    refine LinearMap.mem_range.mpr ⟨prism A (g t₀) (m + 2) (cm A ρ (m + 2) b) - ∑ t, n t • e t, ?_⟩

    rw [map_sub, map_sum, eq_sub_of_add_eq hS]
    simp only [map_smul, he, mul_inv_cancel_left]

    simp only [map_add (f := _), map_sub, map_sum, map_smul, h3, hk, ← h2, hincl1, hincl2, hincl3]
    simp only [smul_sub, Finset.sum_sub_distrib]
    abel
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LatticeBlockClasses.CGtNe

section

@[expose] public section

open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.KL UpperTheory.V.ZK UpperTheory.V.ZK.Cl

theorem UpperTheory.V.ZK.Cl.cGtNe :
    UpperTheory.V.ZK.Cl.CGtNe := by
  intro hS L F _ _ _ _ _ J _ q _ ζ χ η 𝔡 h
  classical
  have hsum : ∀ x : ZMod q, ∑ i : {j // χ j = x}, η i.1 = 0 := by
    intro x
    have h1 : η.mapDomain χ x = 0 := by rw [h]; rfl
    rw [Finsupp.mapDomain, Finsupp.sum_fintype _ _ (by simp), Finsupp.finsetSum_apply] at h1
    rw [← h1, ← Finset.sum_subtype (Finset.univ.filter fun j => χ j = x) (by simp) (fun j => η j), Finset.sum_filter]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finsupp.single_apply]
  have hex : ∀ x : ZMod q, ∃ g : ({j // χ j = x} → F) ≃ₗ[F] ({j // χ j = x} → F), LinearEquiv.det g = 1 ∧
      ∀ w, InLat 0 w ↔ InLat (fun i : {j // χ j = x} => η i.1 • 𝔡) (g w) := by
    intro x
    refine hS F {j // χ j = x} 0 (fun i => η i.1 • 𝔡) 1 (Or.inr rfl) fun P => ?_
    simp only [Pi.zero_apply, Finsupp.coe_zero, sub_zero, Finsupp.smul_apply, smul_eq_mul]
    rw [← Finset.sum_mul, hsum, zero_mul]
    simp [ordP]
  choose g' hdet hlat using hex
  obtain ⟨⟨g, hg⟩, hall⟩ := cBlock L F J (ZMod q) (fun _ => 1) χ g'
  refine ⟨g, (hall g hg).2.2 _ (fun j => η j • 𝔡) (fun j P => ?_) hlat, fun _ => 1, χ, g', hg, fun j => ?_, hdet⟩
  · rw [(cAct L F).2.2.1]
  · congr 1
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LatticeBlockClasses.CSupp

section

@[expose] public section

open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.KL UpperTheory.V.ZK UpperTheory.V.ZK.Cl

theorem UpperTheory.V.ZK.Cl.cSupp :
    UpperTheory.V.ZK.Cl.CSupp := by
  intro L F _ _ _ _ _ 𝔡 b₀ hb₀
  refine ⟨b₀ * ∏ P ∈ 𝔡.support, ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 L), ?_, dvd_mul_right _ _, ?_⟩
  · refine mul_ne_zero hb₀ (Finset.prod_ne_zero_iff.mpr fun P _ => ?_)
    have h : Ideal.absNorm P.asIdeal ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr P.ne_bot
    exact_mod_cast h
  · intro P hP
    rw [map_mul, map_prod]
    apply Ideal.mul_mem_left
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem
      (fun Q : HeightOneSpectrum (𝓞 F) =>
        algebraMap (𝓞 L) (𝓞 F) ((Ideal.absNorm Q.asIdeal : ℕ) : 𝓞 L))
      (Finsupp.mem_support_iff.mpr hP)
    rw [hc]
    apply Ideal.mul_mem_right
    rw [map_natCast]
    exact Ideal.absNorm_mem P.asIdeal
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LatticeBlockClasses.CTriv

section

@[expose] public section

open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.KL UpperTheory.V.ZK UpperTheory.V.ZK.Cl

theorem UpperTheory.V.ZK.Cl.cTriv :
    UpperTheory.V.ZK.Cl.CTriv := by
  intro k _ A _ m θ hθ H V P U
  intro _ _ _ _ _ _ _ _ _ _ μ φ z hz
  obtain ⟨-, hnat, hcomp, -, hsub⟩ := sChain A
  have cyc : ∀ {G G' : Type} [Group G] [Group G'] (f : G →* G') (w : Ch A G (m + 1)),
      Cyc w → Cyc (cm A f (m + 1) w) := by
    intro G G' _ _ f w hw
    unfold Cyc at hw ⊢
    rw [hnat, hw, map_zero]
  rw [hcomp, hθ.iso (V × P) U φ _ (cyc _ _ hz), hθ.add H V P μ 1 z hz]
  have htriv : (θ P) (cm A (1 : H →* P ≃ₗ[k] P) (m + 1) z) = 0 := by
    apply hθ.bdry
    have hf : (1 : H →* P ≃ₗ[k] P) = (1 : Unit →* P ≃ₗ[k] P).comp (1 : H →* Unit) := by
      ext h x
      rfl
    rw [hf, hcomp]
    obtain ⟨w, hw⟩ := hsub Unit m _ (cyc (1 : H →* Unit) z hz)
    rw [← hw, ← hnat]
    exact ⟨_, rfl⟩
  rw [htriv, add_zero]
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LatticeBlockClasses.CUnit

section

@[expose] public section

open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.KL UpperTheory.V.ZK UpperTheory.V.ZK.Cl

theorem UpperTheory.V.ZK.Cl.cUnit :
    UpperTheory.V.ZK.Cl.CUnit := by
  intro L F _ _ _ _ _ k _ r b hb q v
  obtain ⟨_, hmul, hone, hmem, hinv, hadd, hpow⟩ := cAct L F
  have hres := (cRes L F k r).2.2.2 b hb |>.2
  have h1 : ∀ P : HeightOneSpectrum (𝓞 F), ordP P 1 = 0 := fun P => by
    simpa using hpow P 1 0
  let U : Subgroup Fˣ :=
    { carrier := {x | IsBU b x}
      mul_mem' := fun {x y} hx hy P hP => by rw [hadd, hx P hP, hy P hP, add_zero]
      one_mem' := fun P _ => h1 P
      inv_mem' := fun {x} hx P hP => by
        have := hpow P x (-1)
        rw [zpow_neg_one] at this
        rw [this, hx P hP, mul_zero] }
  have uniq : ∀ (x : Fˣ) (u u' : kˣ), Res r x u → Res r x u' → u = u' := by
    rintro x u u' ⟨a, c, hc, hxc, hac⟩ ⟨a', c', hc', hxc', hac'⟩
    have e0 : ((a * c' : 𝓞 F) : F) = ((a' * c : 𝓞 F) : F) := by
      push_cast
      linear_combination (-(c' : F)) * hxc + (c : F) * hxc'
    have e : a * c' = a' * c := by exact_mod_cast e0
    have e2 := congrArg r e
    rw [map_mul, map_mul, hac, hac'] at e2
    have : (u : k) = u' := by
      have hcc : r c * r c' ≠ 0 := mul_ne_zero hc hc'
      apply mul_right_cancel₀ hcc
      linear_combination e2
    exact Units.ext this
  classical
  let f : Fˣ → ZMod q := fun x =>
    if h : ∃ u, Res r x u then Multiplicative.toAdd (v h.choose) else 0
  have fspec : ∀ (x : Fˣ) (u : kˣ), Res r x u → f x = Multiplicative.toAdd (v u) := by
    intro x u hu
    have h : ∃ u, Res r x u := ⟨u, hu⟩
    simp only [f, dif_pos h]
    rw [uniq x _ _ h.choose_spec hu]
  have resmul : ∀ (x y : Fˣ) (u w : kˣ), Res r x u → Res r y w → Res r (x * y) (u * w) := by
    rintro x y u w ⟨a, c, hc, hxc, hac⟩ ⟨a', c', hc', hxc', hac'⟩
    refine ⟨a * a', c * c', by rw [map_mul]; exact mul_ne_zero hc hc', ?_, ?_⟩
    · push_cast
      linear_combination (y * (c' : F)) * hxc + (a : F) * hxc'
    · rw [map_mul, map_mul, hac, hac', Units.val_mul]
      ring
  refine ⟨U, f, fun x => Iff.rfl, ?_, ?_, ?_, fspec, fun x hx => hres x hx⟩
  · intro σ x hx P hP
    have hQ : actP σ (actP σ⁻¹ P) = P := by rw [← hmul, mul_inv_cancel, hone]
    have hb' : (algebraMap (𝓞 L) (𝓞 F)) b ∉ (actP σ⁻¹ P).asIdeal := by
      rw [← hmem σ (actP σ⁻¹ P) b, hQ]
      exact hP
    have := hinv σ (actP σ⁻¹ P) x
    rw [hQ] at this
    rw [this]
    exact hx _ hb'
  · intro x hx y hy
    obtain ⟨u, hu⟩ := hres x hx
    obtain ⟨w, hw⟩ := hres y hy
    rw [fspec _ _ (resmul x y u w hu hw), fspec _ _ hu, fspec _ _ hw, map_mul, toAdd_mul]
  · have h11 : Res r 1 1 := ⟨1, 1, by simp, by simp, by simp⟩
    rw [fspec _ _ h11, map_one, toAdd_one]
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SClassOf

section

@[expose] public section

open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.KL UpperTheory.V.ZK UpperTheory.V.ZK.Cl

theorem UpperTheory.V.ZK.sClassOf :
    UpperTheory.V.ZK.SClassOf :=
  cJoin cChain cFree cTriv cAct cSplit cSupp cLatLoc cMu cInt cVal cGtNe cGtEq cBetaDiv cBetaVal cRep cUnit
end
end
