module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LitAut
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.IsLevel
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.ExistsOpen
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.Factor
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.InfVec
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.OpenLev
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.SpanKeep
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.SpanSph
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeightTraceProducts.WeightDeterminantTwists.FinMH
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.ContCoef
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.DcMap
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.IsoCopy
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.IsoTypic
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.SecSpec
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TLocEig
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Linter.Style
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TSpanEig

section

@[expose] public section




section
open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL Formalism.BasicNotions
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z.Sym.Al
theorem UpperTheory.V.Z.Sym.Al.exists_eigenvector_in_span_of_comp_eq_trivial :
    _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (π : Submodule ℂ (UA L n → ℂ)), IsAutRepU π →
        ∀ w : Plc L, IsSplitAt w → ∀ (W : Sig.Lev (Kw w)) ψ, CompEq π w ψ → (∀ i, ∀ u ∈ W.H, ψ i u = 1) →
        ∀ φ : UA L n → V, φ ≠ 0 → CoefIn φ π →
        ∃ φ', φ' ≠ 0 ∧ InSpan w φ φ' ∧ (∀ x ∈ locU n w, cLoc w x ∈ W.J n → ∀ g, φ' (g * x) = φ' g) ∧ EigT φ' w W ψ := by
  intro hLit L _ _ _ n V _ _ _ π hπ w hw W ψ ⟨hsm, τ, hτ, ⟨e⟩⟩ hψ φ hφ hc
  obtain ⟨s1, -, s3, -⟩ := secSpec L n w hw
  let N : Submodule ℂ (UA L n → V) := Submodule.span ℂ {ψ' | ∃ x ∈ locU n w, ψ' = fun g => φ (g * x)}
  let ρ : Representation ℂ (GL (Fin n) (Kw w)) (UA L n → V) := (rightReg ℂ (UA L n) V).comp (secW n w)
  have hρ : ∀ h (a : UA L n → V) g, ρ h a g = a (g * secW n w h) := fun _ _ _ => rfl
  have hst : ∀ h, ∀ a ∈ N, ρ h a ∈ N := by
    intro h a ha
    refine Submodule.span_induction (p := fun a _ => ρ h a ∈ N) ?_ (by simp) (fun _ _ _ _ h1 h2 => by
      rw [map_add (f := _)]; exact N.add_mem h1 h2) (fun c _ _ h1 => by rw [map_smul]; exact N.smul_mem c h1) ha
    rintro _ ⟨x, hx, rfl⟩
    refine Submodule.subset_span ⟨secW n w h * x, (locU n w).mul_mem (s1 h) hx, ?_⟩
    funext g
    rw [hρ, mul_assoc]
  let ν : Representation ℂ (GL (Fin n) (Kw w)) N :=
    { toFun := fun h => (ρ h).restrict (hst h)
      map_one' := by ext; simp
      map_mul' := fun x y => by ext; simp }
  have hν : ∀ h (a : N), ((ν h a : N) : UA L n → V) = ρ h a := fun _ _ => rfl
  have hφN : φ ∈ N := Submodule.subset_span ⟨1, (locU n w).one_mem, by funext g; rw [mul_one]⟩
  have hco : ∀ a : N, CoefIn (a : UA L n → V) π := fun a =>
    (spanKeep L n V w φ a a.2).1 π hπ hc
  let b := Module.finBasis ℂ V
  let q : Fin (Module.finrank ℂ V) → N →ₗ[ℂ] π := fun i =>
    { toFun := fun a => ⟨b.coord i ∘ (a : UA L n → V), hco a _⟩
      map_add' := fun x y => Subtype.ext (by funext g; simp)
      map_smul' := fun c x => Subtype.ext (by funext g; simp) }
  haveI : Nontrivial N := ⟨⟨⟨φ, hφN⟩, 0, fun h => hφ (congrArg Subtype.val h)⟩⟩
  obtain ⟨f, hf0, hf⟩ := (isoCopy _ _ _ τ.ρ ((repOn hπ).comp (secW n w)) τ.irred
    (isoTypic L n π hπ w hw τ hτ)).2 N (Fin (Module.finrank ℂ V)) ν q
      (fun i h x => Subtype.ext rfl)
      (fun x hx => Subtype.ext (by
        funext g
        refine b.ext_elem fun i => ?_
        have : b.repr ((x : UA L n → V) g) i = 0 := congrFun (congrArg Subtype.val (hx i)) g
        simpa using this)) inferInstance
  have hinj : Function.Injective f := by
    haveI := τ.irred
    let Φ : τ.ρ.IntertwiningMap ν :=
      { toFun := f
        map_add' := f.map_add
        map_smul' := f.map_smul
        isIntertwining' := fun g => LinearMap.ext fun x => hf g x }
    refine (Representation.IsIrreducible.injective_or_eq_zero Φ).resolve_right fun h => hf0 ?_
    exact LinearMap.ext fun x => congrArg (fun Ψ : τ.ρ.IntertwiningMap ν => Ψ x) h
  obtain ⟨v, hv0, hvJ, hvE⟩ := _root_.UpperTheory.V.Z.Sym.Al.exists_fixd_dc_eq_expo_smul_of_equiv_prinSeries hLit (Kw w) n W ψ hsm hψ τ.V τ.ρ ⟨e⟩
  refine ⟨f v, fun h => hv0 (hinj (Subtype.ext (by simpa using h))), (f v).2, ?_, ?_⟩
  · intro x hx hJ g
    have h1 := hf (cLoc w x) v
    rw [hvJ _ hJ] at h1
    have h2 := congrFun (congrArg Subtype.val h1) g
    rw [hν, hρ, s3 x hx] at h2
    exact h2.symm
  · intro d hd
    have h1 := dcMap W τ.ρ ρ (N.subtype ∘ₗ f) (fun h x => by simp [hf, hν]) (Sig.dg d) v
    rw [hvE d hd] at h1
    simpa [EigAt, ρ] using h1.symm
end
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TInVec

section

@[expose] public section




section
open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL Formalism.BasicNotions
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z.Sym.Al
private theorem thinOut {α β : Type} [DecidableEq α] (f : α → β) (S T : Finset α) (hinj : Set.InjOn f (S : Set α)) :
    ∃ T' : Finset α, S ⊆ T' ∧ Set.InjOn f (T' : Set α) ∧ (∀ t ∈ T', t ∉ S → ∀ s ∈ S, f s ≠ f t) ∧
      ∀ t ∈ T, ∃ t' ∈ T', f t' = f t := by
  induction T using Finset.induction_on with
  | empty => exact ⟨S, subset_rfl, hinj, fun t h h' => absurd h h', by simp⟩
  | insert a T₀ _ ih =>
    obtain ⟨T', h1, h2, h3, h4⟩ := ih
    by_cases h : ∃ t' ∈ T', f t' = f a
    · refine ⟨T', h1, h2, h3, fun t ht => ?_⟩
      rcases Finset.mem_insert.1 ht with rfl | ht
      · exact h
      · exact h4 t ht
    · push_neg at h
      refine ⟨insert a T', h1.trans (Finset.subset_insert _ _), ?_, ?_, ?_⟩
      · intro x hx y hy hxy
        rcases Finset.mem_insert.1 (Finset.mem_coe.1 hx) with h₁ | h₁ <;>
          rcases Finset.mem_insert.1 (Finset.mem_coe.1 hy) with h₂ | h₂
        · rw [h₁, h₂]
        · subst h₁
          exact absurd hxy.symm (h y h₂)
        · subst h₂
          exact absurd hxy (h x h₁)
        · exact h2 h₁ h₂ hxy
      · intro t ht htS s hs
        rcases Finset.mem_insert.1 ht with rfl | ht
        · exact h s (h1 hs)
        · exact h3 t ht htS s hs
      · intro t ht
        rcases Finset.mem_insert.1 ht with rfl | ht
        · exact ⟨_, Finset.mem_insert_self _ _, rfl⟩
        · obtain ⟨t', a', b⟩ := h4 t ht
          exact ⟨t', Finset.mem_insert_of_mem a', b⟩
section
variable {L : Type} [Field L] [NumberField L] [IsCMField L]
private theorem away_congr {n : ℕ} {w w' : Plc L} (h : w.under (𝓞 (Lp L)) = w'.under (𝓞 (Lp L))) :
    away n w = away n w' := by
  simp only [away, h]
private theorem cLoc_away {n : ℕ} {w : Plc L} {y : UA L n} (hy : y ∈ away n w) : cLoc w y = 1 :=
  Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hy w) rfl
private noncomputable def AT (S : Finset (Plc L)) (W : ∀ w : Plc L, Sig.Lev (Kw w)) (T : Finset (Plc L)) : Subgroup (UA L 2) :=
  lev (Kall L 2) S W ⊓ ⨅ w ∈ T, away 2 w
private theorem step [DecidableEq (Plc L)] {V : Type} [AddCommGroup V] [Module ℂ V] (S T₀ : Finset (Plc L))
    (W : ∀ w : Plc L, Sig.Lev (Kw w)) (w : Plc L)
    (hS : ∀ v ∈ S, v ≠ w → v.under (𝓞 (Lp L)) ≠ w.under (𝓞 (Lp L)))
    (hT : ∀ t ∈ T₀, t.under (𝓞 (Lp L)) ≠ w.under (𝓞 (Lp L)))
    (R : Representation ℂ (InfinitePlace L → GL (Fin 2) ℂ) V) (φ φ' : UA L 2 → V)
    (hspan : InSpan w φ φ') (hAF : IsAF R (AT S W (insert w T₀)) φ)
    (hinv : ∀ x ∈ locU 2 w, x ∈ Kall L 2 → (w ∈ S → cLoc w x ∈ (W w).J 2) → ∀ g, φ' (g * x) = φ' g) :
    IsAF R (AT S W T₀) φ' := by
  have h1 : AT S W (insert w T₀) ≤ away 2 w :=
    inf_le_right.trans (iInf₂_le w (Finset.mem_insert_self _ _))
  have h2 := (spanKeep L 2 V w φ φ' hspan).2.1 R _ h1 hAF
  refine ⟨h2.left, h2.inf, ?_⟩
  intro u hu g
  obtain ⟨x, hx, y, hy, rfl⟩ := (factor L 2 w).2.1 u
  obtain ⟨hlev, hTa⟩ := Subgroup.mem_inf.1 hu
  obtain ⟨hK, hJ⟩ := Subgroup.mem_inf.1 hlev
  have hxy := ((factor L 2 w).2.2.2.2.2 x hx y hy).1 hK
  have hJ' : ∀ v ∈ S, cLoc v (x * y) ∈ (W v).J 2 := fun v hv =>
    Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hJ v) hv
  have hyw : cLoc w y = 1 := cLoc_away hy
  have hyA : y ∈ AT S W (insert w T₀) := by
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨hxy.2, ?_⟩, ?_⟩
    · refine Subgroup.mem_iInf.2 fun v => Subgroup.mem_iInf.2 fun hv => ?_
      show cLoc v y ∈ (W v).J 2
      by_cases hvw : v = w
      · subst hvw
        rw [hyw]
        exact one_mem _
      · have hxv : cLoc v x = 1 :=
          cLoc_away ((factor L 2 v).2.2.1 w (hS v hv hvw).symm hx)
        have := hJ' v hv
        rwa [map_mul, hxv, one_mul] at this
    · refine Subgroup.mem_iInf.2 fun t => Subgroup.mem_iInf.2 fun ht => ?_
      rcases Finset.mem_insert.1 ht with rfl | ht
      · exact hy
      · have hxt : x ∈ away 2 t := (factor L 2 t).2.2.1 w (hT t ht).symm hx
        have hxyt : x * y ∈ away 2 t := Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hTa t) ht
        exact (Subgroup.mul_mem_cancel_left _ hxt).1 hxyt
  rw [← mul_assoc, h2.level y hyA, hinv x hx hxy.1 ?_]
  intro hwS
  have := hJ' w hwS
  rwa [map_mul, hyw, mul_one] at this
end
theorem UpperTheory.V.Z.Sym.Al.inVec_alt :
    _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (π : Submodule ℂ (UA L 2 → ℂ)), IsAutRepU π → ∀ j : ℕ,
        (∀ v : InfinitePlace L, ∃ lam, HasWeightAt π v.embedding lam ∧ lam.w 0 - lam.w 1 = j) →
        ∀ S : Finset (Plc L), Places (S : Set (Plc L)) →
        (∀ w : Plc L, (∀ w' ∈ S, w'.under (𝓞 (Lp L)) ≠ w.under (𝓞 (Lp L))) → IsUnramU π w) →
        ∀ (W : ∀ w : Plc L, Sig.Lev (Kw w)) (ψ : ∀ w : Plc L, Fin 2 → (Kw w)ˣ →* ℂˣ),
        (∀ w ∈ S, CompEq π w (ψ w) ∧ ∀ i, ∀ u ∈ (W w).H, ψ w i u = 1) →
        ∃ (e : InfinitePlace L → ℤ) (φ : UA L 2 → Wt.VD (InfinitePlace L) j), φ ≠ 0 ∧ IsAF (repE j e) (lev (Kall L 2) S W) φ ∧
          ∀ w ∈ S, EigT φ w (W w) (ψ w) := by
  intro hN L _ _ _ π hπ j hwt S hS hun W ψ hψ
  classical
  haveI : FiniteDimensional ℂ (Wt.VD (InfinitePlace L) j) := Wt.finMH (InfinitePlace L) 2 _
  obtain ⟨e, φ₀, hne, hco, hAF⟩ := infVec L π hπ j hwt
  obtain ⟨U, hUo, hUi⟩ := openLev L 2 _ π hπ φ₀ hco
  obtain ⟨T, hT⟩ := (cof L 2).1 U hUo
  obtain ⟨T', hST, hthin, hsep, hcov⟩ := thinOut (fun w : Plc L => w.under (𝓞 (Lp L))) S T hS.inj
  have key : ∀ D : Finset (Plc L), D ⊆ T' →
      ∃ φ : UA L 2 → Wt.VD (InfinitePlace L) j, φ ≠ 0 ∧ CoefIn φ π ∧ IsAF (repE j e) (AT S W (T' \ D)) φ ∧
        ∀ w ∈ S, w ∉ T' \ D → EigT φ w (W w) (ψ w) := by
    intro D
    induction D using Finset.induction_on with
    | empty =>
      intro _
      refine ⟨φ₀, hne, hco, ⟨hAF.left, hAF.inf, fun u hu g => hUi u ?_ g⟩, fun w hw hw' => ?_⟩
      · obtain ⟨hlev, hTa⟩ := Subgroup.mem_inf.1 hu
        refine hT (Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hlev).1, ?_⟩)
        refine Subgroup.mem_iInf.2 fun t => Subgroup.mem_iInf.2 fun ht => ?_
        obtain ⟨t', ht', hf⟩ := hcov t ht
        rw [← away_congr hf]
        exact Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hTa t') (by simpa using ht')
      · exact absurd (by simpa using hST hw) hw'
    | insert w D₀ hwD ih =>
      intro hsub
      have hwT : w ∈ T' := hsub (Finset.mem_insert_self _ _)
      obtain ⟨φ, hφ, hc, hA, hE⟩ := ih ((Finset.subset_insert _ _).trans hsub)
      have hins : T' \ D₀ = insert w (T' \ insert w D₀) := by
        ext t
        by_cases h : t = w
        · subst h; simp [hwT, hwD]
        · simp [h]
      have hTs : ∀ t ∈ T' \ insert w D₀, t.under (𝓞 (Lp L)) ≠ w.under (𝓞 (Lp L)) := by
        intro t ht hf
        have ht' := Finset.mem_sdiff.1 ht
        exact ht'.2 (by rw [hthin (Finset.mem_coe.2 ht'.1) (Finset.mem_coe.2 hwT) hf]; exact Finset.mem_insert_self _ _)
      rw [hins] at hA
      have hE' : ∀ v ∈ S, v ≠ w → v ∉ T' \ insert w D₀ → EigT φ v (W v) (ψ v) := by
        intro v hv hvw hvT
        refine hE v hv ?_
        rw [hins]
        simp [hvw, hvT]
      by_cases hwS : w ∈ S
      · have hSs : ∀ v ∈ S, v ≠ w → v.under (𝓞 (Lp L)) ≠ w.under (𝓞 (Lp L)) :=
          fun v hv hvw hf => hvw (hS.inj (Finset.mem_coe.2 hv) (Finset.mem_coe.2 hwS) hf)
        obtain ⟨φ', hφ', hspan, hinv, hEig⟩ :=
          _root_.UpperTheory.V.Z.Sym.Al.exists_eigenvector_in_span_of_comp_eq_trivial hN L 2 _ π hπ w (hS.split w hwS) (W w) (ψ w) (hψ w hwS).1 (hψ w hwS).2 φ hφ hc
        have hk := spanKeep L 2 _ w φ φ' hspan
        refine ⟨φ', hφ', hk.1 π hπ hc, step S _ W w hSs hTs _ φ φ' hspan hA
          (fun x hx _ hJ g => hinv x hx (hJ hwS) g), fun v hv hvT => ?_⟩
        by_cases hvw : v = w
        · subst hvw; exact hEig
        · exact fun d hd => hk.2.2 v (hS.split v hv) (hSs v hv hvw) _ d _ (hE' v hv hvw hvT d hd)
      · have hSs : ∀ v ∈ S, v ≠ w → v.under (𝓞 (Lp L)) ≠ w.under (𝓞 (Lp L)) :=
          fun v hv _ => hsep w hwT hwS v hv
        obtain ⟨φ', hφ', hspan, hinv⟩ :=
          spanSph L 2 _ π hπ w (hun w (hsep w hwT hwS)) φ hφ hc
        have hk := spanKeep L 2 _ w φ φ' hspan
        refine ⟨φ', hφ', hk.1 π hπ hc, step S _ W w hSs hTs _ φ φ' hspan hA
          (fun x hx hK _ g => hinv x ⟨hx, hK⟩ g), fun v hv hvT => ?_⟩
        have hvw : v ≠ w := fun h => hwS (h ▸ hv)
        exact fun d hd => hk.2.2 v (hS.split v hv) (hSs v hv hvw) _ d _ (hE' v hv hvw hvT d hd)
  obtain ⟨φ, hφ, -, hA, hE⟩ := key T' subset_rfl
  refine ⟨e, φ, hφ, ⟨hA.left, hA.inf, fun u hu g => hA.level u ?_ g⟩, fun w hw => hE w hw (by simp)⟩
  exact Subgroup.mem_inf.2 ⟨hu, by simp⟩
end
end
end
