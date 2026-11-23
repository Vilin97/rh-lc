module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatCDefs
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatDefs
public import Mathlib.RingTheory.DividedPowers.DPMorphism
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Sheaves.Init
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistFrobeniusFiltrationCompat

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeIsDPMorphismOfCompat

section

@[expose] public section

open DividedPowers CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.LatDP

theorem γB_map {W B W' B' : Type} [CommRing W] [CommRing B] [Algebra ℚ B] [CommRing W'] [CommRing B']
    [Algebra ℚ B'] (f : W →+* B) (ξ : W) (f' : W' →+* B') (ξ' : W') (g : B →+* B') {y : B}
    (hy : y ∈ Lat.IB f ξ) (hy' : g y ∈ Lat.IB f' ξ') (n : ℕ) :
    g ((Lat.γB f ξ).dpow n y) = (Lat.γB f' ξ').dpow n (g y) := by
  have h1 := (Lat.γB f ξ).factorial_mul_dpow_eq_pow (n := n) hy
  have h2 := (Lat.γB f' ξ').factorial_mul_dpow_eq_pow (n := n) hy'
  have hu : IsUnit (n.factorial : B') := by
    have := (IsUnit.mk0 (n.factorial : ℚ) (by exact_mod_cast n.factorial_ne_zero)).map (algebraMap ℚ B')
    rwa [map_natCast] at this
  apply hu.mul_left_cancel
  rw [h2, ← map_pow, ← h1, map_mul, map_natCast]

theorem isDPMorphism_map {W B W' B' : Type} [CommRing W] [CommRing B] [Algebra ℚ B] [CommRing W']
    [CommRing B'] [Algebra ℚ B'] (f : W →+* B) (ξ : W) (f' : W' →+* B') (ξ' : W') (l M : ℕ)
    (g : B →+* B') (hmap : ∀ x ∈ Lat.sub f ξ l M, g x ∈ Lat.sub f' ξ' l M) (u : W')
    (hg : g (f ξ) = f' (u * ξ')) (hc : Lat.DPClosed (Lat.ι f ξ l M) (Lat.γB f ξ))
    (hc' : Lat.DPClosed (Lat.ι f' ξ' l M) (Lat.γB f' ξ')) :
    IsDPMorphism (Lat.γ f ξ l M hc) (Lat.γ f' ξ' l M hc') (Lat.map f ξ f' ξ' l M g hmap) := by
  have hB : ∀ x ∈ Lat.I f ξ l M, g (Lat.ι f ξ l M x) ∈ Lat.IB f' ξ' := by
    intro x hx
    have hx' : Lat.ι f ξ l M x ∈ Lat.IB f ξ := hx
    simp only [Lat.IB, Ideal.mem_span_singleton] at hx' ⊢
    obtain ⟨c, hc0⟩ := hx'
    refine ⟨f' u * g c, ?_⟩
    rw [hc0, map_mul, hg, map_mul]; ring
  have hI : ∀ x ∈ Lat.I f ξ l M, Lat.map f ξ f' ξ' l M g hmap x ∈ Lat.I f' ξ' l M := by
    intro x hx
    show Lat.ι f' ξ' l M (Lat.map f ξ f' ξ' l M g hmap x) ∈ Lat.IB f' ξ'
    rw [Lat.ι_map]; exact hB x hx
  refine ⟨Ideal.map_le_iff_le_comap.2 fun x hx => hI x hx, fun {n} x hx => ?_⟩
  apply Lat.ι_injective f' ξ' l M
  rw [Lat.ι_γ f' ξ' l M hc' (hI x hx)]
  simp only [Lat.ι_map]
  rw [Lat.ι_γ f ξ l M hc hx]
  have hx' : Lat.ι f ξ l M x ∈ Lat.IB f ξ := hx
  exact (γB_map f ξ f' ξ' g hx' (hB x hx) n).symm

end GlobalTheory.CompanionTheory.LatDP
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelGaloisIsDPMorphism

section

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

namespace GlobalTheory.CompanionTheory.LatSigDP

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ}

theorem exists_gB_xi (h : LevHyp l K M) (k : ℕ) (g : K.fixingSubgroup) :
    ∃ u : Ainf l, gB h k g (fk l k (xi0 l)) = fk l k (u * xi0 l) := by
  obtain ⟨u, hu⟩ := GlobalTheory.CompanionTheory.TwFil.exists_gal_xi (toBot g.1)
  refine ⟨u, ?_⟩
  have e : galBdRHom (toBot g.1) (wittToBDeRhamPlus (normInteger ℂ_[l]) l (xi0 l)) =
      wittToBDeRhamPlus (normInteger ℂ_[l]) l (u * xi0 l) := by
    rw [← hu, ← gal_smul_wittToBDeRhamPlus]
    rfl
  show Ideal.Quotient.mk _ (galBdRHom (toBot g.1) (wittToBDeRhamPlus (normInteger ℂ_[l]) l (xi0 l))) = _
  rw [e]
  rfl

theorem sigA_isDPMorphism (h : LevHyp l K M) (k : ℕ) (g : K.fixingSubgroup) :
    IsDPMorphism (lev h k).γ (lev h k).γ ((lev h k).σA g) := by
  obtain ⟨u, hu⟩ := exists_gB_xi h k g
  exact GlobalTheory.CompanionTheory.LatDP.isDPMorphism_map (fk l k) (xi0 l) (fk l k) (xi0 l) l M (gB h k g) (h.gal k g) u hu
    (h.hc k) (h.hc k)

end GlobalTheory.CompanionTheory.LatSigDP
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelGaloisIsDPMorphismStatement

section

@[expose] public section

open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

theorem _root_.GlobalTheory.T.level_galois_isDPMorphism : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ} (h : LevHyp l K M) (k : ℕ), ∀ g, IsDPMorphism (lev h k).γ (lev h k).γ ((lev h k).σA g) := by
  first | exact @GlobalTheory.CompanionTheory.LatSigDP.sigA_isDPMorphism | exact GlobalTheory.CompanionTheory.LatSigDP.sigA_isDPMorphism | (intros; apply GlobalTheory.CompanionTheory.LatSigDP.sigA_isDPMorphism <;> assumption)
end
end
