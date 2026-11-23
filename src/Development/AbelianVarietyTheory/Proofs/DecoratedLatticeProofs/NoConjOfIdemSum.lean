module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SplitPart
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AltENsmulLeft
public import Formalism.LocalToGlobal.KernelLattices.XiIndCClass
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThCLeftStab
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemFin
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemSplit
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.AlternatingFormStandardHermitian
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FiniteDimensionalMram

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CocRZeroLeft

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.L2.Ker

noncomputable section

namespace GlobalTheory.SemiTwist

variable {E : Type} [Field E] [NumberField E] [StarRing E] {ι : Type} [Fintype ι] {a b : ℕ}
  (emb : ι → E →+* ℂ) (δ : ℂ) (d : ℕ) (sc : ℝ)

def cocR (x y : Formalism.L2.Col.HomE E a b) : ℝ :=
  (Real.sqrt d * (HV (ι := ι) sc (embH emb δ x) (embH emb δ y)).re +
    Formalism.L2.Th1.H.altE (HV sc) (embH emb δ x) (embH emb δ y)) / 2

theorem cocR_add_left (x y z : Formalism.L2.Col.HomE E a b) :
    cocR emb δ d sc (x + y) z = cocR (ι := ι) emb δ d sc x z + cocR emb δ d sc y z := by
  simp only [cocR, Formalism.L2.Th1.H.altE, map_add (f := _), LinearMap.add_apply, Complex.add_re, Complex.add_im]; ring

theorem cocR_zero_left (z : Formalism.L2.Col.HomE E a b) : cocR (ι := ι) emb δ d sc 0 z = 0 := by
  simp [cocR, Formalism.L2.Th1.H.altE]

theorem hv_embH_smul (hconj : ∀ τ x, emb τ (star x) = starRingEnd ℂ (emb τ x)) (r : E) (x y : Formalism.L2.Col.HomE E a b) :
    HV (ι := ι) sc (embH emb δ (r • x)) (embH emb δ y) = HV sc (embH emb δ x) (embH emb δ (star r • y)) := by
  simp only [HV, LinearMap.mk₂'ₛₗ_apply, embH, AddMonoidHom.coe_mk, ZeroHom.coe_mk, LinearMap.smul_apply, Pi.smul_apply,
    smul_eq_mul, map_mul, hconj, Complex.conj_conj]
  congr 1
  refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem cocR_smul (hconj : ∀ τ x, emb τ (star x) = starRingEnd ℂ (emb τ x)) (r : E) (x y : Formalism.L2.Col.HomE E a b) :
    cocR (ι := ι) emb δ d sc (r • x) y = cocR emb δ d sc x (star r • y) := by
  simp only [cocR, Formalism.L2.Th1.H.altE, hv_embH_smul emb δ sc hconj]

theorem semiChar_twO : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (ι : Type) [Fintype ι] [Nonempty ι] (a b : ℕ) (emb : ι → E →+* ℂ) (δ : ℂ) (d : ℕ) (sc : ℝ) (M : Submodule (𝓞 E) (Formalism.L2.Col.HomE E a b)) (c : ℕ) (e : HeightOneSpectrum (𝓞 E) → ℤ), δ ≠ 0 → (∀ (τ : ι) (x : E), emb τ (star x) = starRingEnd ℂ (emb τ x)) → 0 < c → (∀ Q, e (Formalism.L2.Col.conjPrime₂ Q) = -e Q) → (∀ Q, e Q = 1 ∨ e Q = 0 ∨ e Q = -1) → Formalism.L2.Th1.H.IsSelfDual (HV sc) (laV emb δ M) → Formalism.L2.Th1.H.IsSemiChar (HV sc) (laV emb δ M) (alV d sc) → Formalism.L2.Th1.H.IsSemiChar (HV sc) (laV emb δ (twist₂ M c e)) (alV d sc) := by
  intro E _ _ _ ι _ _ a b emb δ d sc M c e _ hconj hc he _ _ hM
  have hH : Formalism.L2.Th1.H.IsHerm (HV (ι := ι) (a := a) (b := b) sc) := fun x y => by
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Formalism.L2.Ker.HV, map_sum, mul_comm]
  have h0 : ∀ x ∈ M, ∀ y ∈ M, ∃ n : ℤ, cocR emb δ d sc x y = n := fun x hx y hy =>
    (GlobalTheory.KerLaw.semi_iff hH (Real.sqrt d) _).1 hM (embH emb δ x) ⟨x, hx, rfl⟩ (embH emb δ y) ⟨y, hy, rfl⟩
  refine (GlobalTheory.KerLaw.semi_iff hH (Real.sqrt d) _).2 ?_
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  change ∃ n : ℤ, cocR emb δ d sc x y = n
  let I : Ideal (𝓞 E) :=
    { carrier := {r | ∀ s : 𝓞 E, ∃ n : ℤ, cocR emb δ d sc ((s * r) • x) y = n}
      zero_mem' := fun s => ⟨0, by simp [cocR_zero_left]⟩
      add_mem' := fun {r r'} hr hr' s => by
        obtain ⟨n, hn⟩ := hr s
        obtain ⟨m, hm⟩ := hr' s
        exact ⟨n + m, by rw [mul_add, add_smul, cocR_add_left, hn, hm, Int.cast_add]⟩
      smul_mem' := fun t r hr s => by
        rw [smul_eq_mul, ← mul_assoc]
        exact hr _ }
  have hI : I = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    let Q : HeightOneSpectrum (𝓞 E) :=
      ⟨m, hm.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hm (RingOfIntegers.not_isField E)⟩
    obtain ⟨u, hu, hx⟩ := (Formalism.L2.Col.mem_locP _ _ _).1 ((GlobalTheory.KerLaw.mem_tw _ _ _ _).1 hx Q)
    obtain ⟨v, hv, hy⟩ := (Formalism.L2.Col.mem_locP _ _ _).1 ((GlobalTheory.KerLaw.mem_tw _ _ _ _).1 hy (Formalism.L2.Col.conjPrime₂ Q))
    rw [he, zpow_neg, inv_inv] at hy
    have hmem : u * Formalism.L2.Col.cO E v ∈ I := by
      intro s
      obtain ⟨n, hn⟩ := h0 _ (Submodule.smul_mem _ s hx) _ hy
      refine ⟨n, ?_⟩
      rw [← hn]
      have e1 : (s * (u * Formalism.L2.Col.cO E v)) • x =
          (star (algebraMap (𝓞 E) E v) * (c : E) ^ e Q) • (s • u • ((c : E) ^ e Q)⁻¹ • x) := by
        rw [← algebraMap_smul E s, ← algebraMap_smul E u, ← algebraMap_smul E (s * _), smul_smul, smul_smul, smul_smul,
          map_mul, map_mul, Formalism.L2.Col.algebraMap_cO]
        congr 1
        have hk : (c : E) ^ e Q ≠ 0 := zpow_ne_zero _ (Nat.cast_ne_zero.2 hc.ne')
        field_simp
      rw [e1, cocR_smul emb δ d sc hconj, star_mul', star_star, star_zpow₀, star_natCast, mul_smul, algebraMap_smul]
    rcases hm.isPrime.mem_or_mem (hle hmem) with h' | h'
    · exact hu h'
    · exact hv h'
  have : (1 : 𝓞 E) ∈ I := hI ▸ Submodule.mem_top
  simpa using this 1

end GlobalTheory.SemiTwist
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NoConjOfIdemSum

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HalfSplit

theorem noConj_of_idemSum : ∀ (D : D7) (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → ∀ P ∈ SS, Formalism.L2.Col.conjPrime₂ P ∉ SS := by
  intro D e SS hI P hP hP'
  obtain ⟨⟨es, hes, he⟩, hc⟩ := hI
  have h1 : ∀ i ∈ SS, es i * es i = es i := fun i hi => (hes i hi).1.1
  have hcross : ∀ i ∈ SS, ∀ j ∈ SS, es i * cA D (es j) = 0 := by
    subst he
    exact GlobalTheory.PlaceDatum.cross_eq_zero (R := AE D) GlobalTheory.PlaceDatum.isUnit_natCast (cA D) es SS h1 hc
  have hcj : Lev.IsConjPl (D := D) (Formalism.L2.Col.conjPrime₂ P) P := by
    intro c hc'
    exact ⟨Formalism.L2.Col.cO D.host.E c, (Formalism.L2.Col.mem_conjP P c).1 hc', rfl⟩
  have heq : es P = cA D (es (Formalism.L2.Col.conjPrime₂ P)) :=
    Formalism.IndefR.Fin.conj_idem_eq (hes _ hP') (hes P hP) hcj
  apply Formalism.IndefR.Fin.idemAt_ne_zero (hes P hP)
  have := hcross P hP _ hP'
  rw [← heq, h1 P hP] at this
  exact this

theorem splitHyp_halves : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → ∀ (N : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (c : ℕ), 0 < c → Odd c → (∀ Q ∈ SS, ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal) → LaFacts (tauE D) δ D.host.d sc (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N' → IsSelfDualC S N → IsSelfDualC T N' → SplitHyp (HV sc) (alV D.host.d sc) (AC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) SS N N' c) (BC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) SS N N' c) (LamC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') := by
  intro D ψ θ S T δ sc hP e SS hI N N' c hc hcS h2 hL hN hN'
  have hSS : ∀ P ∈ SS, Formalism.L2.Col.conjPrime₂ P ∉ SS := noConj_of_idemSum D e SS hI
  have hT : Nonempty D.what₂.Tau := ⟨D.eTau.symm (Classical.arbitrary _)⟩
  have hconj : ∀ τ (x : D.host.E), tauE D τ (star x) = starRingEnd ℂ (tauE D τ x) := fun τ x =>
    GlobalTheory.FockCompare.tauE_star τ x
  have he1 : ∀ Q, expS SS Q = 1 ∨ expS SS Q = 0 ∨ expS SS Q = -1 := by
    intro Q; unfold expS; split_ifs <;> simp
  have hc1 : ∀ Q, expS SS (Formalism.L2.Col.conjPrime₂ Q) = -expS SS Q := exponent_set_conjugate D.host.E SS hSS
  have hfg : N.FG := hN.1.fg
  have tw : ∀ f : HeightOneSpectrum (𝓞 D.host.E) → ℤ, (∀ Q, f (Formalism.L2.Col.conjPrime₂ Q) = -f Q) →
      (∀ Q, f Q = 1 ∨ f Q = 0 ∨ f Q = -1) →
      LaFacts (tauE D) δ D.host.d sc (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N (twist₂ N' c f) := by
    intro f hf1 hf2
    unfold LaFacts LamC
    rw [← twist_homomorphism D.host.E _ _ _ N N' c f hfg hc]
    exact ⟨GlobalTheory.TwPerSelfDual.twO_selfDual D.host.E D.what₂.Tau _ _ (tauE D) δ D.host.d sc _ c f hP.ne hconj hc hf1 hf2 hL.1 hL.2,
      GlobalTheory.SemiTwist.semiChar_twO D.host.E D.what₂.Tau _ _ (tauE D) δ D.host.d sc _ c f hP.ne hconj hc hf1 hf2 hL.1 hL.2⟩
  exact half_periods_of_lattice D.host.E D.what₂.Tau _ _ (tauE D) δ D.host.d sc _ SS N N' c hP.ne hc hSS hfg hL
    (tw _ hc1 he1) (tw (fun Q => -expS SS Q) (fun Q => by simp [hc1])
      (fun Q => by rcases he1 Q with h | h | h <;> simp [h]))

end GlobalTheory.HalfSplit
end
end
end
