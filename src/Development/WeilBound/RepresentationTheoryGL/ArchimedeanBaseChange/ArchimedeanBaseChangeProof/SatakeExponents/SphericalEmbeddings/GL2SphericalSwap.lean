module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SphericalEmbeddings.StageLift
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SphericalEmbeddings.GL2LinkedPair
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SphericalEmbeddings.NoLinkRev
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SphericalEmbeddings.PseSat
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
import Mathlib.Algebra.Order.Star.Int
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SphericalEmbeddings.PseSat
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NotInSupportOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalRepGLExistsSatakeParameters
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JordanHolderMultiplicityNormalizedBorelJacquetUn
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.BernsteinZelevinskyFiniteness
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SphericalEmbeddings.PseStage

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SphericalEmbeddings.PseAsm

section

@[expose] public section

namespace PositivityTheory.Rg.BcB.N3.Pse

open PositivityTheory.Rg.BcB.N3 GlobalTheory.SmGL

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem sphEmb_of (hG : GL2SphericalSwap k) (hS : StageLift k) (hE : ExpSph k) (hP : SatPerm k) (hB : Bubble k) : SphEmb k := by
  intro n ξ hm V _ _ π hs hi hsph hq
  obtain ⟨η, f, hf⟩ := hE n V π hs hi hsph
  obtain ⟨σ, rfl⟩ := hP n ξ η V π hs hi hsph hq ⟨f, hf⟩
  exact hB hS hG n ξ hm σ V π hi hsph ⟨f, PositivityTheory.Rg.BcB.N3.PseSat.injective_of_ne_zero hi f hf⟩

end PositivityTheory.Rg.BcB.N3.Pse
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SphericalEmbeddings.PseBub

section

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel

namespace PositivityTheory.Rg.BcB.N3.PseBub

open PositivityTheory.Rg.BcB.N3 PositivityTheory.Rg.BcB.N3.Pse PositivityTheory.Rg.BcB.N3.PseSat

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem comp_injective {n : ℕ} {V W U : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup U] [Module ℂ U] {π : Representation ℂ (GL (Fin n) k) V} {ρ : Representation ℂ (GL (Fin n) k) W}
    {τ : Representation ℂ (GL (Fin n) k) U} (hi : π.IsIrreducible) (hsph : IsSpherical π)
    (f : π.IntertwiningMap ρ) (hf : Function.Injective f) (T : ρ.IntertwiningMap τ) (hT : KInj k T) :
    Function.Injective (T.comp f) := by
  classical
  set g := T.comp f with hg
  have hg' : ∀ v, g v = T (f v) := fun v => Representation.IntertwiningMap.comp_apply _ _ _ T f v
  rcases hi.eq_bot_or_eq_top (Representation.IntertwiningMap.ker _ _ g) with h | h
  · intro x y hxy
    have hx : x - y ∈ Representation.IntertwiningMap.ker _ _ g := by
      rw [Representation.IntertwiningMap.mem_ker, map_sub, hxy, sub_self]
    rw [h] at hx
    have hx' : x - y ∈ (⊥ : Submodule ℂ V) := hx
    exact sub_eq_zero.1 ((Submodule.mem_bot ℂ).1 hx')
  · exfalso
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hsph
    have hfv : f v ∈ fixed ρ (KO k (Fin n)) := by
      intro h'
      have := hv h'
      rw [← Representation.IntertwiningMap.isIntertwining, this]
      simp
    have hker : v ∈ Representation.IntertwiningMap.ker _ _ g := by
      rw [h]
      exact (Submodule.mem_top : v ∈ (⊤ : Submodule ℂ V))
    rw [Representation.IntertwiningMap.mem_ker, hg'] at hker
    have := hT (f v) hfv hker
    exact hv0 (hf (by rw [this, map_zero]))

def wt {n : ℕ} (σ : Equiv.Perm (Fin n)) : ℕ := ∑ i : Fin n, (i : ℕ) * (σ i : ℕ)

theorem wt_le {n : ℕ} (σ : Equiv.Perm (Fin n)) : wt σ ≤ n * (n * n) := by
  unfold wt
  calc ∑ i : Fin n, (i : ℕ) * (σ i : ℕ) ≤ ∑ _i : Fin n, n * n :=
        Finset.sum_le_sum fun i _ => Nat.mul_le_mul i.2.le (σ i).2.le
    _ = n * (n * n) := by simp

theorem wt_swap {n : ℕ} (σ : Equiv.Perm (Fin n)) (i j : Fin n) (hij : (j : ℕ) = i + 1) (hd : σ j < σ i) :
    wt σ < wt (σ * Equiv.swap i j) := by
  classical
  have hne : i ≠ j := by
    intro h
    subst h
    omega
  unfold wt
  have key : ∀ τ : Equiv.Perm (Fin n), ∑ k : Fin n, (k : ℕ) * (τ k : ℕ) =
      (i : ℕ) * (τ i : ℕ) + ((j : ℕ) * (τ j : ℕ) +
        ∑ k ∈ (Finset.univ.erase i).erase j, (k : ℕ) * (τ k : ℕ)) := by
    intro τ
    rw [Finset.add_sum_erase (Finset.univ.erase i) (fun k : Fin n => (k : ℕ) * (τ k : ℕ))
      (Finset.mem_erase.2 ⟨hne.symm, Finset.mem_univ j⟩)]
    rw [Finset.add_sum_erase Finset.univ (fun k : Fin n => (k : ℕ) * (τ k : ℕ)) (Finset.mem_univ i)]
  rw [key σ, key (σ * Equiv.swap i j)]
  have hrest : ∑ k ∈ (Finset.univ.erase i).erase j, (k : ℕ) * ((σ * Equiv.swap i j) k : ℕ) =
      ∑ k ∈ (Finset.univ.erase i).erase j, (k : ℕ) * (σ k : ℕ) := by
    apply Finset.sum_congr rfl
    intro k hk
    have hkj := Finset.ne_of_mem_erase hk
    have hki := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hk)
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hki hkj]
  rw [hrest, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_right]
  have hd' : (σ j : ℕ) < σ i := hd
  rw [hij]
  nlinarith

theorem exists_descent {n : ℕ} (σ : Equiv.Perm (Fin n)) (h1 : σ ≠ 1) :
    ∃ i j : Fin n, (j : ℕ) = i + 1 ∧ σ j < σ i := by
  by_contra hne
  push_neg at hne
  apply h1
  cases n with
  | zero => exact Subsingleton.elim _ _
  | succ m =>
    have hs : StrictMono (σ : Fin (m + 1) → Fin (m + 1)) := by
      rw [Fin.strictMono_iff_lt_succ]
      intro i
      have hle := hne i.castSucc i.succ (by simp)
      exact lt_of_le_of_ne hle (fun h => (Fin.castSucc_lt_succ (i := i)).ne (σ.injective h))
    ext x
    have hx := congrFun hs.eq_id x
    simp [hx]

theorem bubble : Bubble k := by
  intro hSL hG2 n ξ hξ σ₀ V _ _ π hi hsph hf₀
  have key : ∀ m : ℕ, ∀ σ : Equiv.Perm (Fin n), n * (n * n) - wt σ = m →
      (∃ f : π.IntertwiningMap (iP (ξ ∘ ⇑σ)), Function.Injective ⇑f) →
        ∃ f : π.IntertwiningMap (iP ξ), Function.Injective ⇑f := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro σ hm hσ
      by_cases h1 : σ = 1
      · subst h1
        exact hσ
      · obtain ⟨i, j, hij, hd⟩ := exists_descent σ h1
        obtain ⟨f, hf⟩ := hσ
        have hle : ‖(((ξ ∘ ⇑σ) i : ℂˣ) : ℂ)‖ ≤ ‖(((ξ ∘ ⇑σ) j : ℂˣ) : ℂ)‖ := hξ _ _ hd.le
        obtain ⟨T0, hT0⟩ := hG2 _ _ hle
        obtain ⟨T, hT⟩ := hSL n (ξ ∘ ⇑σ) i j hij ⟨T0, hT0⟩
        have hinj := comp_injective hi hsph f hf T hT
        have hw := wt_swap σ i j hij hd
        have hwle := wt_le (σ * Equiv.swap i j)
        have hlt : n * (n * n) - wt (σ * Equiv.swap i j) < m := by
          generalize n * (n * n) = N at *
          omega
        exact ih _ hlt (σ * Equiv.swap i j) rfl ⟨T.comp f, hinj⟩
  exact key _ σ₀ rfl hf₀

end PositivityTheory.Rg.BcB.N3.PseBub
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SphericalEmbeddings.PseExp

section

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel

namespace PositivityTheory.Rg.BcB.N3.PseExp

open PositivityTheory.Rg.BcB.N3 PositivityTheory.Rg.BcB.N3.Pse

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_map_of_eigenform {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GL (Fin n) k) V} (hπ : IsSmooth π)
    (μ : (Fin n → kˣ) →* ℂˣ) (l : Jacquet π (unipB k (Fin n)) →ₗ[ℂ] ℂ) (hl0 : l ≠ 0)
    (hl : ∀ t x, l (jacB π t x) = (μ t : ℂ) * l x) :
    ∃ f : π.IntertwiningMap (indB (ofChar μ)), f ≠ 0 := by
  let ρ : Representation ℂ (Levi k fun _ : Fin n => Unit) ℂ :=
    (ofChar μ).comp (leviTorus k (Fin n)).symm.toMonoidHom
  let φ : (jac (points (Fin n)) π).IntertwiningMap ρ :=
    ⟨l, fun g => LinearMap.ext fun x => by
      obtain ⟨t, rfl⟩ := (leviTorus k (Fin n)).surjective g
      have e : (ρ (leviTorus k (Fin n) t)) (l x) = (μ t : ℂ) * l x := by
        show ofChar μ ((leviTorus k (Fin n)).symm (leviTorus k (Fin n) t)) _ = _
        rw [MulEquiv.symm_apply_apply, ofChar_apply]
      exact (hl t x).trans e.symm⟩
  obtain ⟨f, hf⟩ := (GlobalTheory.SmGL.Model.evalOne_bijective (points (Fin n)) hπ ρ).2 φ
  refine ⟨f, fun h0 => hl0 (LinearMap.ext fun x => ?_)⟩
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have h1 : φ (Submodule.Quotient.mk v) = (f v).1.1 1 := by rw [← hf]; rfl
  have h2 : l (Submodule.Quotient.mk v) = φ (Submodule.Quotient.mk v) := rfl
  rw [h2, h1, h0]
  rfl

theorem expSph : ExpSph k := by
  intro n V _ _ π hs hi hsph
  have hadm : IsAdmissible π := (GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness k).1 (Fin n) V π hs hi
  have hI : fixed π (iwahori k (Fin n)) ≠ ⊥ := by
    obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hsph
    refine (Submodule.ne_bot_iff _).2 ⟨v, fun h => ?_, hv0⟩
    exact hv ⟨h.1, iwahori_le_KO k _ h.2⟩
  obtain ⟨χ, l, hl0, hl, hχ⟩ := GlobalTheory.SatakeExists.exists_eigenform_jacBU hadm hI
  let δ : (Fin n → kˣ) →* ℂˣ :=
    (deltaHalf k fun _ : Fin n => Unit).comp (leviTorus k (Fin n)).toMonoidHom
  obtain ⟨α, hα⟩ := GlobalTheory.SatakeExists.exists_eq_torusChar (χ * δ⁻¹) fun t ht => by
    have : δ t = 1 := GlobalTheory.SmGL.UnramFixed.deltaHalf_torusO k ht
    simp [hχ t ht, this]
  obtain ⟨f, hf⟩ := exists_map_of_eigenform hadm.1 (χ * δ⁻¹) l hl0 fun t x => by
    rw [GlobalTheory.SmGL.UnramFixed.jacB_apply, map_smul, hl, smul_eq_mul, MonoidHom.mul_apply, Units.val_mul,
      MonoidHom.inv_apply]
    ring
  refine ⟨α, ?_⟩
  show ∃ f : π.IntertwiningMap (indB (ofChar (torusChar fun i => unrChar k (α i)))), f ≠ 0
  rw [hα]
  exact ⟨f, hf⟩

end PositivityTheory.Rg.BcB.N3.PseExp
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SphericalEmbeddings.GL2SphericalSwap

section

@[expose] public section

namespace PositivityTheory.Rg.BcB.N3.Pse

open PositivityTheory.Rg.BcB.N3 GlobalTheory.SmGL

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem GL2_spherical_swap : GL2SphericalSwap k := fun a b hab => by
  by_cases hL : unrChar k a = unrChar k b * absPow k 1
  · exact PositivityTheory.Rg.BcB.N3.GL2LinkedPair.linked a b hL
  · exact unl a b hL hab

theorem sphEmb : SphEmb k :=
  sphEmb_of k (GL2_spherical_swap k) (PositivityTheory.Rg.BcB.N3.PseStage.stageLift k) PositivityTheory.Rg.BcB.N3.PseExp.expSph
    PositivityTheory.Rg.BcB.N3.PseSat.satPerm PositivityTheory.Rg.BcB.N3.PseBub.bubble

end PositivityTheory.Rg.BcB.N3.Pse
end
end
