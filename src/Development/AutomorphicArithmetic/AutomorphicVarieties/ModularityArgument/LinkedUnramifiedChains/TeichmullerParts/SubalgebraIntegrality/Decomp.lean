module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.UnramifiedTrivialInertialType
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueAdmissibleLocalComponentDefiniteUnit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalComponentLevelFixedVectorsNeBotStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAutFormsWeightLevelFiniteSumFixedVectorsStatement
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.EventuallyMemHeckeLevelAndIwahoriCongruence
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.PlaceBetween
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.WtOfForm
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.SubalgebraIntegrality.DecompA
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.ContinuousTorusCharacter
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.SubalgebraIntegrality.DecompC

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.SubalgebraIntegrality.DecompB

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.V.Hi

namespace UpperTheory.V.Z.J.D.Dc

theorem core3 {E : Type} [Field E] [NumberField E] [IsCMField E] {n m d : ℕ} {Γ Ga Gp D Jx : Type} [Group Γ] [Group Ga]
    [Group Gp] [AddCommGroup D] [Module ℂ D] [FiniteDimensional ℂ D] [Fintype Jx] (X : Frame Γ Ga Gp)
    (ξ : Gp →* GL (Fin d) ℂ) (τ : X.Ub →* GL (Fin m) ℂ) (U₀ : Subgroup X.Ub) (I : Subgroup Gp) (J : UA E n →* Ga × Gp)
    (tf : (Ga × Gp → Fin d → ℂ) →ₗ[ℂ] D →ₗ[ℂ] (UA E n → ℂ)) (r : UA E n → D → D)
    (hJinf : ∀ x ∈ infU E n, J x = 1) (hRfin : ∀ k ∈ finU (E := E) (n := n), ∀ ℓ, r k ℓ = ℓ)
    (hinj : ∀ F ∈ X.AF ξ, (∀ ℓ, tf F ℓ = 0) → F = 0)
    (haut : ∀ F ∈ X.AF ξ, IsOpen {k : finU (E := E) (n := n) | ∀ g, F (g * J k) = F g} → ∀ ℓ, IsAutFormU (tf F ℓ))
    (htr : ∀ F ℓ x, RU E n x (tf F ℓ) = tf (fun g => F (g * J x)) (r x ℓ))
    (hsurj : Function.Surjective fun k : finU (E := E) (n := n) => J k)
    (hsur : ∀ Φ : D →ₗ[ℂ] (UA E n → ℂ), (∀ ℓ, IsAutFormU (Φ ℓ)) → (∀ ℓ, ∀ x ∈ infU E n, RU E n x (Φ ℓ) = Φ (r x ℓ)) →
      ∃ F ∈ X.AF ξ, ∀ ℓ, tf F ℓ = Φ ℓ)
    (hev : ∀ᶠ k : finU (E := E) (n := n) in nhds 1, (∃ u ∈ U₀, (u : Ga) = (J k).1 ∧ τ u = 1) ∧ (J k).2 ∈ I)
    (Kf : Subgroup (finU (E := E) (n := n))) (hKf : ∀ k ∈ Kf, (∃ u ∈ U₀, (u : Ga) = (J k).1 ∧ τ u = 1) ∧ (J k).2 ∈ I)
    (Pw : Submodule ℂ (UA E n → ℂ) → Prop)
    (hwt : ∀ σ, IsAutRepU σ → (Submodule.pi Set.univ (fun _ => X.AF ξ) ⊓ fixd (X.raF d τ) U₀) ⊓
      Submodule.span ℂ {F : Fin m → X.Fn ℂ d | ∀ i ℓ, tf (F i) ℓ ∈ σ} ≠ ⊥ → Pw σ)
    (σ : Jx → Submodule ℂ (UA E n → ℂ)) (hσ : ∀ j, IsAutRepU (σ j)) (hind : iSupIndep σ)
    (hcov : ∀ π, IsAutRepU π → Pw π → π ⊓ GlobalTheory.PRep.fixed (GlobalTheory.BCT.RF E n) Kf ≤ ⨆ j, σ j)
    (F : Fin m → X.Fn ℂ d) (hF : F ∈ Submodule.pi Set.univ (fun _ => X.AF ξ) ⊓ fixd (X.raF d τ) U₀)
    (hb : F ∈ fixd (X.rpF ℂ d m) I) :
    F ∈ ⨆ j, ((Submodule.pi Set.univ (fun _ => X.AF ξ) ⊓ fixd (X.raF d τ) U₀) ⊓
      Submodule.span ℂ {F : Fin m → X.Fn ℂ d | ∀ i ℓ, tf (F i) ℓ ∈ σ j}) ⊓ fixd (X.rpF ℂ d m) I := by
  have hra : ∀ (u : X.Ub) (G : Fin m → Ga × Gp → Fin d → ℂ) (i : Fin m),
      X.raF d τ u G i = ∑ j, (τ u).val i j • fun g => G j (g * ((u : Ga), 1)) := fun u G i => by
    funext g t
    rw [Finset.sum_apply, Finset.sum_apply]
    rfl
  choose k1 hk1 using fun u : U₀ => hsurj (((u : X.Ub) : Ga), 1)
  choose k2 hk2 using fun p : I => hsurj (1, (p : Gp))
  let T : U₀ ⊕ I → (Ga × Gp → Fin d → ℂ) → (Ga × Gp → Fin d → ℂ) :=
    Sum.elim (fun u G g => G (g * (((u : X.Ub) : Ga), 1))) (fun p G g => G (g * (1, (p : Gp))))
  let kk : U₀ ⊕ I → UA E n := Sum.elim (fun u => (k1 u : UA E n)) (fun p => (k2 p : UA E n))
  let a : U₀ ⊕ I → Fin m → Fin m → ℂ := Sum.elim (fun u => (τ u.1).val) (fun _ => (1 : Matrix (Fin m) (Fin m) ℂ))
  have hone : ∀ (p : I) (G : Fin m → Ga × Gp → Fin d → ℂ) (i : Fin m),
      ∑ j, a (.inr p) i j • T (.inr p) (G j) = T (.inr p) (G i) := fun p G i => by
    rw [Finset.sum_eq_single i (fun j _ hj => by
      change (1 : Matrix (Fin m) (Fin m) ℂ) i j • _ = 0
      rw [Matrix.one_apply_ne hj.symm, zero_smul]) (fun h => (h (Finset.mem_univ _)).elim)]
    change (1 : Matrix (Fin m) (Fin m) ℂ) i i • _ = _
    rw [Matrix.one_apply_eq, one_smul]
  have hfixG : ∀ G : Fin m → Ga × Gp → Fin d → ℂ, (∀ u i, ∑ j, a u i j • T u (G j) = G i) →
      ∀ k : finU (E := E) (n := n), ((∃ u ∈ U₀, (u : Ga) = (J k).1 ∧ τ u = 1) ∧ (J k).2 ∈ I) → ∀ i g, G i (g * J k) = G i g := by
    rintro G hG k ⟨⟨u, hu, huk, h1⟩, hk⟩ i g
    have h2 : ∑ j, (τ u).val i j • (fun g => G j (g * ((u : Ga), 1))) = G i := hG (.inl ⟨u, hu⟩) i
    rw [h1] at h2
    have h3 : ∀ g, G i (g * ((u : Ga), 1)) = G i g := fun g => by
      have h4 := congrFun h2 g
      rw [Finset.sum_apply, Finset.sum_eq_single i (fun j _ hj => by
        rw [Units.val_one, Matrix.one_apply_ne hj.symm, zero_smul]; rfl) (fun h => (h (Finset.mem_univ _)).elim),
        Units.val_one, Matrix.one_apply_eq, one_smul] at h4
      exact h4
    have h5 : ∀ g, G i (g * (1, (J k).2)) = G i g := fun g => by
      have h6 := (hone ⟨_, hk⟩ G i).symm.trans (hG (.inr ⟨_, hk⟩) i)
      exact congrFun h6 g
    have h6 : J k = ((u : Ga), 1) * (1, (J k).2) := Prod.ext (huk.symm.trans (mul_one _).symm) (one_mul _).symm
    rw [h6, ← mul_assoc, h5, h3]
  have hFA : ∀ i, F i ∈ X.AF ξ := fun i => hF.1 i trivial
  have hinvF : ∀ u i, ∑ j, a u i j • T u (F j) = F i := by
    rintro (u | p) i
    · exact (hra u.1 F i).symm.trans (congrFun (hF.2 u.1 u.2) i)
    · exact (hone p F i).trans (congrFun (hb p.1 p.2) i)
  obtain ⟨G, hGA, hGi, hGσ, hsum⟩ := absMain (X.AF ξ) tf r hinj hsur T kk a
    (by
      rintro (u | p) G hG γ g
      · have := hG γ (g * (((u : X.Ub) : Ga), 1))
        rw [← mul_assoc] at this
        exact this
      · have := hG γ (g * (1, (p : Gp)))
        rw [← mul_assoc] at this
        exact this)
    (by
      rintro (u | p) G ℓ
      · have h1 := htr G ℓ (k1 u)
        rw [hRfin _ (k1 u).2, show J (k1 u) = _ from hk1 u] at h1
        exact h1.symm
      · have h1 := htr G ℓ (k2 p)
        rw [hRfin _ (k2 p).2, show J (k2 p) = _ from hk2 p] at h1
        exact h1.symm)
    (GlobalTheory.PRep.fixed (GlobalTheory.BCT.RF E n) Kf) Pw
    (fun G hGA hG i ℓ => haut (G i) (hGA i) (by
      let S : Subgroup (finU (E := E) (n := n)) :=
        { carrier := {k | ∀ g, G i (g * J k) = G i g}
          one_mem' := fun g => by rw [OneMemClass.coe_one, map_one, mul_one]
          mul_mem' := fun {x y} hx hy g => by rw [Subgroup.coe_mul, map_mul, ← mul_assoc, hy, hx]
          inv_mem' := fun {x} hx g => by rw [← hx, Subgroup.coe_inv, map_inv, inv_mul_cancel_right] }
      refine S.isOpen_of_mem_nhds (g := 1) ?_
      filter_upwards [hev] with k hk g
      exact hfixG G hG k hk i g) ℓ)
    (fun G _ ℓ x hx => by
      have h1 := htr G ℓ x
      simp only [hJinf x hx, mul_one] at h1
      exact h1)
    (fun G _ hG i ℓ k => by
      have h1 := htr (G i) ℓ (k.1 : UA E n)
      rw [hRfin _ k.1.2] at h1
      have h2 : (fun g => G i (g * J (k.1 : UA E n))) = G i := funext (hfixG G hG k.1 (hKf k.1 k.2) i)
      rw [h2] at h1
      simp only [MonoidHom.one_apply, Units.val_one, one_smul]
      exact h1)
    (fun σ' hσ' G hGA hG h0 hm => hwt σ' hσ' fun hbot => h0 <| by
      have hmem : G ∈ (Submodule.pi Set.univ (fun _ => X.AF ξ) ⊓ fixd (X.raF d τ) U₀) ⊓
          Submodule.span ℂ {F : Fin m → X.Fn ℂ d | ∀ i ℓ, tf (F i) ℓ ∈ σ'} :=
        ⟨⟨fun i _ => hGA i, fun u hu => funext fun i => (hra u G i).trans (hG (.inl ⟨u, hu⟩) i)⟩,
          Submodule.subset_span hm⟩
      rw [hbot] at hmem
      exact (Submodule.mem_bot _).1 hmem)
    σ hσ hind hcov F hFA hinvF
  rw [← hsum]
  refine Submodule.sum_mem _ fun j _ => Submodule.mem_iSup_of_mem j ⟨⟨⟨fun i _ => hGA j i, fun u hu =>
    funext fun i => (hra u (G j) i).trans (hGi j (.inl ⟨u, hu⟩) i)⟩, Submodule.subset_span (hGσ j)⟩,
    fun p hp => funext fun i => ?_⟩
  exact (hone ⟨p, hp⟩ (G j) i).symm.trans (hGi j (.inr ⟨p, hp⟩) i)

end UpperTheory.V.Z.J.D.Dc
end
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.SubalgebraIntegrality.Decomp

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing Filter
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj)
open UpperTheory.V.HV (Coef)
open UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.Z.Mult (Cp At IsDec CompOf Mult)
open UpperTheory.V.Z.J.D
open scoped Matrix TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField



private theorem fixOf {L : Type} [Field L] [NumberField L] [IsCMField L] (hU : GlobalTheory.BCT.Unr L) {n : ℕ} (hn : 1 ≤ n)
    {S : Set (GlobalTheory.BCT.Pl L)} (hS : GlobalTheory.BCT.IsSection S) {lam : InfinitePlace L → DomWeight n}
    {K' : ∀ w : GlobalTheory.BCT.Pl L, Subgroup (GlobalTheory.BCT.UL n w)}
    (hLev : GlobalTheory.BCT.IsLevelFam (fun w : GlobalTheory.BCT.Pl L => MonoidHom.id (GlobalTheory.BCT.UL n w)) (GlobalTheory.BCT.KL n) K')
    (π : Submodule ℂ (UA L n → ℂ)) (h1 : IsAutRepU π) (h2 : ∀ v, HasWeightAt π v.embedding (lam v))
    (h3 : π ⊓ GlobalTheory.PRep.fixed (GlobalTheory.BCT.RF L n) (GlobalTheory.BCT.globLev S K') ≠ ⊥) (w : GlobalTheory.BCT.Pl L) (hw : w ∈ S)
    (hs : IsSplitAt w) (τ : SmIrr (GLw n w)) (hc : Cp π w τ) :
    GlobalTheory.PRep.fixed (τ.ρ.comp (GlobalTheory.BCT.UL n w).subtype) (K' w) ≠ ⊥ := by
  have hUL : GlobalTheory.BCT.UL n w = ⊤ := if_pos hs
  have hsurj : Function.Surjective (GlobalTheory.BCT.UL n w).subtype := fun g =>
    ⟨⟨g, hUL ▸ Subgroup.mem_top g⟩, rfl⟩
  let σ₁ : SmIrr (GlobalTheory.BCT.UL n w) :=
    { V := τ.V
      ρ := τ.ρ.comp (GlobalTheory.BCT.UL n w).subtype
      smooth := fun v => (τ.smooth v).preimage continuous_subtype_val
      irred := GlobalTheory.BCT.LocCompU.isIrreducible_comp_of_surjective τ.ρ _ hsurj τ.irred }
  obtain ⟨-, f, hf0, hfm, hf⟩ := hc
  let p : locU n w →* GlobalTheory.BCT.UL n w :=
    ((cLoc w).comp (locU n w).subtype).codRestrict (GlobalTheory.BCT.UL n w) fun x => hUL ▸ Subgroup.mem_top _
  exact GlobalTheory.T.localComponent_levelFixedVectors_ne_bot L hU n hn S hS lam K' hLev π h1 h2 h3 w hw σ₁
    ⟨p, fun x => rfl, σ₁.irred, f, hf0, hfm, fun x v => hf x v⟩

section Tf

variable {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
  [IsAlgClosure L Ω] {s : HidaSetting l L Ω} {n : ℕ} {V : s.Lev} (ι : Qbar l ≃+* ℂ) {lam : Wt L l n} {d : ℕ}
  (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res))

private def tfOf : (Ga l L n × GV n (fun v : V.frame.Vl => s.w v.1) → Fin d → ℂ) →ₗ[ℂ]
    Module.Dual ℂ (⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res)) →ₗ[ℂ] (UA L n → ℂ) :=
  LinearMap.mk₂ ℂ (toForm ι e)
    (fun F F' ℓ => funext fun g => by simp only [toForm, Pi.add_apply, map_add (f := _)])
    (fun a F ℓ => funext fun g => by simp only [toForm, Pi.smul_apply, map_smul])
    (fun F ℓ ℓ' => funext fun g => by simp only [toForm, Pi.add_apply, LinearMap.add_apply])
    (fun a F ℓ => funext fun g => by simp only [toForm, Pi.smul_apply, LinearMap.smul_apply])

private theorem yEq {c : Coef l} {m : ℕ} (Q : QData V) (τ₀ : KT n (wt s) →* GL (Fin m) c.O)
    (ξ : GV n (fun v : V.frame.Vl => s.w v.1) →* GL (Fin d) ℂ) (σ' : Submodule ℂ (UA L n → ℂ)) :
    (Submodule.pi Set.univ (fun _ => (hset Q τ₀).X.AF ξ) ⊓ fixd ((hset Q τ₀).X.raF d ((hset Q τ₀).τC ι)) (hset Q τ₀).UQ) ⊓
      Submodule.span ℂ {F : Fin (hset Q τ₀).m → (hset Q τ₀).X.Fn ℂ d | ∀ i ℓ, tfOf ι e (F i) ℓ ∈ σ'} = YOf Q ι τ₀ e ξ σ' := rfl

end Tf

private theorem wtY {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ) (hn : 1 ≤ n) (V : s.Lev) (Q : QData V) (c : Coef l) (ι : Qbar l ≃+* ℂ)
    (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O) (lam : Wt L l n) (d : ℕ)
    (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res))
    (ξ : GV n (fun v : V.frame.Vl => s.w v.1) →* GL (Fin d) ℂ) (hξ : IsBasis ι e ξ)
    (σ' : Submodule ℂ (UA L n → ℂ)) (hσ' : IsAutRepU σ') (hne : YOf Q ι τ₀ e ξ σ' ≠ ⊥) :
    ∀ y : Emb l (fun v : V.frame.Vl => s.w v.1), HasWeightAt σ' (ι.toRingHom.comp y.res) (lam y.res).dual :=
  UpperTheory.V.Hi.partUR2Wt l L Ω s n hn V Q c ι m τ₀ lam d e ξ hξ σ' hσ' hne

private theorem wtZ {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] {s : HidaSetting l L Ω} {n : ℕ} (V : s.Lev) (ι : Qbar l ≃+* ℂ) (lam : Wt L l n)
    (lam' : InfinitePlace L → DomWeight n) (hlink : WtLink V ι lam lam')
    (σ' : Submodule ℂ (UA L n → ℂ)) (hσ' : IsAutRepU σ')
    (h : ∀ y : Emb l (fun v : V.frame.Vl => s.w v.1), HasWeightAt σ' (ι.toRingHom.comp y.res) (lam y.res).dual) :
    ∀ v, HasWeightAt σ' v.embedding (lam' v) :=
  (hlink σ' hσ').1 h

private def PwD {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} (lam' : InfinitePlace L → DomWeight n)
    (π : Submodule ℂ (UA L n → ℂ)) : Prop := ∀ v, HasWeightAt π v.embedding (lam' v)

private theorem levLe {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] {s : HidaSetting l L Ω} {n : ℕ} {V : s.Lev} (Q : QData V) (hQ : IsEmpty Q.Q) {c : Coef l} {m : ℕ}
    (τ₀ : KT n (wt s) →* GL (Fin m) c.O) (K : (hset Q τ₀).Lev) : (hset Q τ₀).lev K ≤ (hset Q τ₀).UQ := by
  unfold HSet.lev
  refine sup_le le_rfl (iSup_le fun q => ?_)
  exact (hQ.false q).elim

private theorem mainStep {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ) (hn : 1 ≤ n) (V : s.Lev) (Q : QData V) (c : Coef l) (ι : Qbar l ≃+* ℂ)
    (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O) (hτ : IsOpen (τ₀.ker : Set (KT n (wt s)))) (lam : Wt L l n) (d : ℕ)
    (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res))
    (ξ : GV n (fun v : V.frame.Vl => s.w v.1) →* GL (Fin d) ℂ) (hξ : IsBasis ι e ξ) (b : ℕ)
    (hQ : IsEmpty Q.Q)
    (Pw : Submodule ℂ (UA L n → ℂ) → Prop)
    (hwtY : ∀ σ' : Submodule ℂ (UA L n → ℂ), IsAutRepU σ' → YOf Q ι τ₀ e ξ σ' ≠ ⊥ → Pw σ')
    (Kf : Subgroup (finU (E := L) (n := n)))
    (hKf : ∀ k ∈ Kf, (∃ u : Ub n s, u ∈ UQ n Q ∧ (u : Ga l L n) = (away l L n).rangeRestrict (k : UA L n) ∧
      τ₀ (toKT n s u) = 1) ∧ (fun v : V.frame.Vl => cLoc (s.w v.1) (k : UA L n)) ∈ (hset Q τ₀).X.I.I1 b)
    {J' : Type} [Fintype J'] (σ : J' → Submodule ℂ (UA L n → ℂ)) (hσ : ∀ j, IsAutRepU (σ j)) (hind : iSupIndep σ)
    (hcov : ∀ π, IsAutRepU π → Pw π → π ⊓ GlobalTheory.PRep.fixed (GlobalTheory.BCT.RF L n) Kf ≤ ⨆ j, σ j) :
    (hset Q τ₀).Big ι ξ ⊓ fixd ((hset Q τ₀).X.rpF ℂ d m) ((hset Q τ₀).X.I.I1 b) ≤
      ⨆ i, YOf Q ι τ₀ e ξ (σ i) ⊓ fixd ((hset Q τ₀).X.rpF ℂ d m) ((hset Q τ₀).X.I.I1 b) := by
  intro F hF
  let J : UA L n →* Ga l L n × GV n (fun v : V.frame.Vl => s.w v.1) :=
    MonoidHom.prod (away l L n).rangeRestrict (Pi.monoidHom fun v : V.frame.Vl => cLoc (s.w v.1))
  obtain ⟨hinj, haut, htr, hsurj, hsur⟩ := UpperTheory.V.Hi.formU l L Ω s n hn V Q c m τ₀ ι lam d e ξ hξ J (fun _ => rfl)
  haveI := e.finiteDimensional
  have hJinf : ∀ x ∈ infU L n, J x = 1 := fun x hx => by
    have h1 : ∀ w, cLoc w x = 1 := fun w => by
      have h2 : Matrix.GeneralLinearGroup.map (pFin L) x.1 = 1 := hx
      change Matrix.GeneralLinearGroup.map (pLoc L w) (Matrix.GeneralLinearGroup.map (pFin L) x.1) = 1
      rw [h2, map_one]
    exact Prod.ext (Subtype.ext (funext fun w => h1 _)) (funext fun v => h1 _)
  have hRfin : ∀ k ∈ finU (E := L) (n := n), infRep (V := V) ι lam k = 1 := fun k hk => by
    have h1 : ∀ τ, cEmb τ k = 1 := fun τ => by
      change Matrix.GeneralLinearGroup.map (coord τ) (cInf k) = 1
      rw [MonoidHom.mem_ker.1 hk, map_one]
    have h2 : (Pi.monoidHom fun e : Emb l (fun v : V.frame.Vl => s.w v.1) =>
        (GlobalTheory.Branching.sqRep ℂ n (lam e.res)).comp (cEmb (E := L) (n := n) (ι.toRingHom.comp e.res))) k = 1 :=
      funext fun y => by
        change GlobalTheory.Branching.sqRep ℂ n (lam y.res) (cEmb _ k) = 1
        rw [h1, map_one]
    unfold infRep
    rw [MonoidHom.comp_apply, h2, map_one]
  refine Dc.core3 (hset Q τ₀).X ξ ((hset Q τ₀).τC ι) (hset Q τ₀).UQ ((hset Q τ₀).X.I.I1 b) J (tfOf ι e)
    (fun x ℓ => ℓ ∘ₗ infRep ι lam x⁻¹) hJinf (fun k hk ℓ => ?_) hinj haut htr hsurj hsur ?_ Kf (fun k hk => ?_) Pw
    (fun σ' hσ' hne => hwtY σ' hσ' (by rw [← yEq ι e Q τ₀ ξ σ']; exact hne))
    σ hσ hind hcov F hF.1 hF.2
  · rw [hRfin _ ((finU (E := L) (n := n)).inv_mem hk)]
    rfl
  · filter_upwards [UpperTheory.eventually_mem_heckeLevel_and_iwahoriCongruence l L Ω s n hn V Q c m τ₀ hτ
      ⟨fun q => (hQ.false q).elim, fun q => (hQ.false q).elim⟩ b] with k ⟨⟨u, hu, huk, hu1⟩, hk⟩
    refine ⟨⟨u, levLe Q hQ τ₀ _ hu, huk, ?_⟩, hk⟩
    change Matrix.GeneralLinearGroup.map _ (τ₀ (toKT n s u)) = 1
    rw [hu1, map_one]
  · obtain ⟨⟨u, hu, huk, hu1⟩, hk'⟩ := hKf k hk
    refine ⟨⟨u, hu, huk, ?_⟩, hk'⟩
    change Matrix.GeneralLinearGroup.map _ (τ₀ (toKT n s u)) = 1
    rw [hu1, map_one]

private theorem yIndep {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ) (hn : 1 ≤ n) (V : s.Lev) (Q : QData V) (c : Coef l) (ι : Qbar l ≃+* ℂ)
    (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O) (lam : Wt L l n) (d : ℕ)
    (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res))
    (ξ : GV n (fun v : V.frame.Vl => s.w v.1) →* GL (Fin d) ℂ) (hξ : IsBasis ι e ξ)
    {J' : Type} (σ : J' → Submodule ℂ (UA L n → ℂ)) (hind : iSupIndep σ) :
    iSupIndep (fun i => YOf Q ι τ₀ e ξ (σ i)) := by
  obtain ⟨hinj, -⟩ := UpperTheory.V.Hi.formU l L Ω s n hn V Q c m τ₀ ι lam d e ξ hξ
    (MonoidHom.prod (away l L n).rangeRestrict (Pi.monoidHom fun v : V.frame.Vl => cLoc (s.w v.1))) (fun _ => rfl)
  let Tt : Fin m × Module.Dual ℂ (⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res)) →
      (Fin m → Ga l L n × GV n (fun v : V.frame.Vl => s.w v.1) → Fin d → ℂ) →ₗ[ℂ] (UA L n → ℂ) :=
    fun t => (LinearMap.applyₗ t.2) ∘ₗ tfOf ι e ∘ₗ LinearMap.proj t.1
  refine Dc.indepOf σ hind _ Tt (fun i y hy t => ?_)
    (fun i y hy h0 => funext fun a => hinj (y a) (hy.1.1 a trivial) fun ℓ => h0 (a, ℓ))
  have hle : Submodule.span ℂ {F : Fin m → Ga l L n × GV n (fun v : V.frame.Vl => s.w v.1) → Fin d → ℂ |
      ∀ a ℓ, toForm ι e (F a) ℓ ∈ σ i} ≤ (σ i).comap (Tt t) := Submodule.span_le.2 fun F hF => hF t.1 t.2
  exact hle hy.2

set_option Elab.async false in
theorem UpperTheory.V.Z.J.D.decomp :
    IndepS → Decomp := by
  intro hI l _ L Ω _ _ _ _ _ _ s n hn V hV Q c ι m τ₀ lam d e ξ hξ hτ lam' hlink b
  have hU := Dc.unrOf s
  obtain ⟨c0, hc0⟩ := Dc.exC (n := n) (s := s) τ₀ hτ
  have hcc := hc0 (c0 + b + 1) (by omega)
  have hfin : s.S.Finite := hV ▸ V.fin
  have hS := Dc.secRange s
  have hLev : GlobalTheory.BCT.IsLevelFam (fun w : GlobalTheory.BCT.Pl L => MonoidHom.id (GlobalTheory.BCT.UL n w)) (GlobalTheory.BCT.KL n)
      (Dc.Kf s n (c0 + b + 1)) := Dc.levFam hfin
  obtain ⟨-, J', hJ', σ, hσ, hind, hsup, -⟩ := GlobalTheory.T.unitaryAutForms_weight_level_finite_sum_fixed_vectors L hU n hn _ hS lam' _ hLev
  have hdec : IsDec (Set.range s.w) lam' (Dc.Kf s n (c0 + b + 1)) σ := ⟨hσ, hind, hsup⟩
  have hσind := hI L n _ hS lam' _ hLev J' σ hdec
  refine ⟨Set.range s.w, Dc.Kf s n (c0 + b + 1), J', hJ', σ, hS, hLev, fun w hw => Dc.Kf_notS hw, hdec,
    yIndep s n hn V Q c ι m τ₀ lam d e ξ hξ σ hσind,
    fun i w hw => Dc.unramOf hU _ (hσ i).2.2 w hw,
    fun i w hw hs τ hc => fixOf hU hn hS hLev (σ i) (hσ i).1 (hσ i).2.1 (hσ i).2.2 w hw hs τ hc, ?_⟩
  have hQ := Dc.Q_empty hV Q
  have hgood : ∀ k ∈ GlobalTheory.BCT.globLev (Set.range s.w) (Dc.Kf s n (c0 + b + 1)),
      (∃ u : Ub n s, u ∈ UQ n Q ∧ (u : Ga l L n) = (away l L n).rangeRestrict (k : UA L n) ∧ τ₀ (toKT n s u) = 1) ∧
        (fun v : V.frame.Vl => cLoc (s.w v.1) (k : UA L n)) ∈ (hset Q τ₀).X.I.I1 b := fun k hk =>
    Dc.goodOf hV Q τ₀ b hcc (by omega) (by omega) hU k hk
  have hwtY : ∀ σ' : Submodule ℂ (UA L n → ℂ), IsAutRepU σ' → YOf Q ι τ₀ e ξ σ' ≠ ⊥ → PwD lam' σ' := fun σ' hσ' hne =>
    wtZ V ι lam lam' hlink σ' hσ' (wtY s n hn V Q c ι m τ₀ lam d e ξ hξ σ' hσ' hne)
  have hcov : ∀ π : Submodule ℂ (UA L n → ℂ), IsAutRepU π → PwD lam' π →
      π ⊓ GlobalTheory.PRep.fixed (GlobalTheory.BCT.RF L n) (GlobalTheory.BCT.globLev (Set.range s.w) (Dc.Kf s n (c0 + b + 1))) ≤ ⨆ j, σ j := by
    intro π hπ hP φ hφ
    have h1 : φ ∈ GlobalTheory.BCT.forms (Set.range s.w) lam' (Dc.Kf s n (c0 + b + 1)) :=
      (le_iSup₂_of_le (f := fun (π : Submodule ℂ (UA L n → ℂ))
        (_ : IsAutRepU π ∧ ∀ v, HasWeightAt π v.embedding (lam' v)) =>
          π ⊓ GlobalTheory.PRep.fixed (GlobalTheory.BCT.RF L n) (GlobalTheory.BCT.globLev (Set.range s.w) (Dc.Kf s n (c0 + b + 1))))
        π ⟨hπ, hP⟩ le_rfl) hφ
    rw [← hsup] at h1
    have h2 : (⨆ i, σ i ⊓ GlobalTheory.PRep.fixed (GlobalTheory.BCT.RF L n) (GlobalTheory.BCT.globLev (Set.range s.w) (Dc.Kf s n (c0 + b + 1)))) ≤ ⨆ j, σ j :=
      iSup_mono fun i => inf_le_left
    exact h2 h1
  exact mainStep s n hn V Q c ι m τ₀ hτ lam d e ξ hξ b hQ
    (PwD lam') hwtY
    (GlobalTheory.BCT.globLev (Set.range s.w) (Dc.Kf s n (c0 + b + 1))) hgood σ (fun j => (hσ j).1) hσind hcov
end
end
end
