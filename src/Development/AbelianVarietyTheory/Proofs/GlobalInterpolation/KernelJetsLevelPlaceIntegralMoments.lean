module

public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.JetSumTable
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EqAndAlg
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TranslateMomentsAll
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AbsNormEqOfSplit
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AbsNormSpanInvol
public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NarrowJetMoments
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.JetSumTable
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TranslateMomentsAll
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AlgebraicNumbersPadicPlacesFacts
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ContinuousToZModComp
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsPrimeUnder
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LocPAAAndPrimesNe
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MemSuppBarOfNe
import Formalism.LocalToGlobal.Columns.BaseLemmas
import Formalism.LocalToGlobal.KernelLattices.XiIndCClass
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NegOneZpowRound
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NotDvdDifferent
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RatIntOfIsIntegral
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RelDetCompanion
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormPadicEmbeddingLeOneOfMemInverseHalfDifferent
import Development.AutomorphicArithmetic.CyclotomicBounds.SmallFacts
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DeltaNeZero
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FieldIsoSelfDualAndPeriodLatticesAgree
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.InterTransport
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormalisedFamilyLatticeHypAndSmooth
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.QuadraticFormIntegralOfSelfDualPeriodLattices
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.IsAdmissibleFlagPairOfUnitriangularLeftAutomorph
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.StdOK
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LatIntZero
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnitPeriodTranslatesMomentsFiniteStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AbsNormSplitPlace

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT

namespace GlobalTheory.Proof.AbsNormSplitPlace

open GlobalTheory.Proof.NarrowJetMoments

theorem absNorm_of_split {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (h2 : Module.finrank F E = 2) {v : HeightOneSpectrum (𝓞 F)} (hs : SplitAt E v) (hl : (Ideal.absNorm v.asIdeal).Prime)
    {P : HeightOneSpectrum (𝓞 E)} (hP : P.asIdeal.under (𝓞 F) = v.asIdeal) :
    Ideal.absNorm P.asIdeal = Ideal.absNorm v.asIdeal := by
  obtain ⟨Q, Q', -, hm⟩ := hs
  have hN : Ideal.absNorm Q.asIdeal * Ideal.absNorm Q'.asIdeal = Ideal.absNorm v.asIdeal ^ 2 := by
    rw [← map_mul, ← hm, Ideal.absNorm_algebraMap]
    congr 1
    rw [← h2]
    exact (Algebra.IsAlgebraic.finrank_of_isFractionRing (𝓞 F) F (𝓞 E) E).symm
  have h1 : ∀ R : HeightOneSpectrum (𝓞 E), Ideal.absNorm R.asIdeal ≠ 1 := fun R h =>
    R.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h)
  have hb := (hl.mul_eq_prime_sq_iff (h1 Q) (h1 Q')).1 hN
  have hle : Q.asIdeal * Q'.asIdeal ≤ P.asIdeal := by
    rw [← hm, ← hP, Ideal.under_def]
    exact Ideal.map_comap_le
  rcases P.isPrime.mul_le.1 hle with h | h
  · rw [← Q.isMaximal.eq_of_le P.isPrime.ne_top h, hb.1]
  · rw [← Q'.isMaximal.eq_of_le P.isPrime.ne_top h, hb.2]

theorem plc_eq_absNorm {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)}
    (hl : (Ideal.absNorm v.asIdeal).Prime) : ringChar (𝓞 F ⧸ v.asIdeal) = Ideal.absNorm v.asIdeal := by
  have h6 : ringChar (𝓞 F ⧸ v.asIdeal) ∣ Ideal.absNorm v.asIdeal := by
    rw [← ringChar.spec, ← map_natCast (Ideal.Quotient.mk v.asIdeal), Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.absNorm_mem _
  haveI := v.isPrime
  exact ((Nat.dvd_prime hl).1 h6).resolve_left CharP.ringChar_ne_one

theorem main : ∀ (Z : Dat) (u : Z.Pr.Word) (sel : HeightOneSpectrum (𝓞 Z.X.F) → HeightOneSpectrum (𝓞 Z.X.E)) (S : Set ℕ) (mu : Tup Z.X.F Z.X.E Z.X.K S), Z.Ok → IsSel Z.X sel → Z.Pr.T u ∈ S → (∀ i, Z.Pr.g i ∈ S) → (∀ P ∈ Sall sel mu u, conjPrime₂ P ∉ Sall sel mu u) ∧ ∀ P ∈ rowSG Z.Pr sel mu, (Formalism.L2.Col.qOf P).Prime ∧ Formalism.L2.Col.qOf P ≠ Z.Pr.T u ∧ ((Z.Pr.T u : ℕ) : 𝓞 Z.X.E) ∉ P.asIdeal ∧ ((∃ i, Formalism.L2.Col.qOf P = Z.Pr.g i) ∨ Formalism.L2.Col.qOf P ∉ S) := by
  intro Z u sel S mu hZ hsel hT hg
  have hPr := hZ.primes
  have hTn : ∀ P ∈ rowSG Z.Pr sel mu, ((Z.Pr.T u : ℕ) : 𝓞 Z.X.E) ∉ P.asIdeal := fun P hP =>
    notMem_rowSG hPr hsel (hPr.T_prime u) hT (hPr.T_ne_g u) hP
  refine ⟨fun P hP hP' => ?_, fun P hP => ?_⟩
  · rcases (mem_Sall sel mu u P).1 hP with h | h <;> rcases (mem_Sall sel mu u _).1 hP' with h' | h'
    · refine conj_piT_notMem hPr u ⟨conjPrime₂ P, h'⟩ ?_
      change cO Z.X.E (Z.Pr.piT u) ∈ (conjPrime₂ P).asIdeal
      rw [mem_conjP, cO_cO]
      exact decoFin_mem_of_mem_divs h
    · exact hTn _ h' (natCast_mem_conjP.2 (T_mem hPr u ⟨P, h⟩))
    · exact hTn _ h (natCast_mem_conjP.1 (T_mem hPr u ⟨conjPrime₂ P, h'⟩))
    · exact conjP_notMem_rowSG hZ.fields hPr hsel hg h h'
  · have key : (Formalism.L2.Col.qOf P).Prime ∧ ((∃ i, Formalism.L2.Col.qOf P = Z.Pr.g i) ∨ Formalism.L2.Col.qOf P ∉ S) := by
      classical
      rcases Finset.mem_union.1 hP with h | h
      · obtain ⟨i, hi⟩ := mem_vGs_iff.1 h
        have e : Formalism.L2.Col.qOf P = Z.Pr.g i := hPr.vG_norm i P hi
        exact ⟨e ▸ hPr.g_prime i, Or.inl ⟨i, e⟩⟩
      · obtain ⟨v, hv, e⟩ := good_of_mem_QE h
        have e1 : Formalism.L2.Col.qOf P = Ideal.absNorm v.asIdeal :=
          absNorm_of_split hZ.fields.rankE hv.1 hv.2.1.1 (e ▸ hsel v)
        refine ⟨e1 ▸ hv.2.1.1, Or.inr ?_⟩
        rw [e1, ← plc_eq_absNorm hv.2.1.1]
        exact hv.2.2
    refine ⟨key.1, fun e => hTn P hP ?_, hTn P hP, key.2⟩
    rw [← e]
    exact Ideal.absNorm_mem _

end GlobalTheory.Proof.AbsNormSplitPlace
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MomentCompanion

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT

namespace GlobalTheory.MomT.MomentCompanion

theorem companion_gen {E : Type} [Field E] [NumberField E] [StarRing E] {b : ℕ}
    {ST SG : Finset (HeightOneSpectrum (𝓞 E))} (ϖ : 𝓞 E) (d : DecoSet (E := E) (n := b) (ST := ST) (SG := SG))
    (hST : ∀ P : ST, ϖ ∈ P.1.asIdeal) (hcop : IsCoprime ϖ (cO E ϖ)) :
    ∃ N'' : Submodule (𝓞 E) (Sp E b), IsSdLat N'' ∧ (∀ y ∈ d.1.N, (ϖ : E) • y ∈ N'') ∧
      (∀ y ∈ N'', star (ϖ : E) • y ∈ d.1.N) ∧
      ∀ (P : ST) (y : Sp E b), y ∈ localization₂ P.1.asIdeal N'' ↔ y ∈ d.1.at P.1 ∧ d.1.f P y = 0 := by
  have hd := d.2
  have hIN : Ideal.span {ϖ} • d.1.N ≤ d.1.L := by
    rw [Submodule.smul_le]
    intro r hr y hy
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hr
    exact hd.smul_N_mem_L (fun P => Ideal.mul_mem_left _ _ (hST P)) hy
  obtain ⟨h1, h2⟩ := glue_unimodular (I := Ideal.span {ϖ}) (J := Ideal.span {cO E ϖ})
    (fun p hp => by
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hp
      rw [map_mul]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _))
    (fun p hp => by
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hp
      rw [map_mul, cO_cO]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _))
    (by
      obtain ⟨u, v, huv⟩ := hcop
      exact ⟨u * ϖ, Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _), v * cO E ϖ,
        Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _), huv⟩)
    hd.uni hd.L_lattice hd.L_le_N hIN
  have hbar : ∀ x ∈ d.1.L ⊔ Ideal.span {ϖ} • dual (hStd E b) d.1.L, cO E ϖ • x ∈ d.1.L := by
    intro x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    rw [smul_add]
    refine Submodule.add_mem _ (Submodule.smul_mem _ _ hy) ?_
    refine Submodule.smul_induction_on hz (fun r hr u hu => ?_) (fun u v hu hv => ?_)
    · rw [smul_comm]
      exact hIN (Submodule.smul_mem_smul hr (conj_smul_dual_mem hd.uni hIN
        (by rw [cO_cO]; exact Ideal.mem_span_singleton_self _) hu))
    · rw [smul_add]
      exact Submodule.add_mem _ hu hv
  refine ⟨_, ⟨h1, h2⟩, fun y hy => ?_, fun y hy => ?_, fun P y => ?_⟩
  · have : ϖ • y ∈ d.1.L := hd.smul_N_mem_L hST hy
    rw [← algebraMap_smul E ϖ y] at this
    exact Submodule.mem_sup_left this
  · have := hd.L_le_N (hbar y hy)
    rw [← algebraMap_smul E (cO E ϖ) y, algebraMap_cO] at this
    exact this
  · have hn : cO E ϖ ∉ P.1.asIdeal := by
      intro h
      obtain ⟨u, v, huv⟩ := hcop
      exact one_notMem P.1 (huv ▸ Ideal.add_mem _ (Ideal.mul_mem_left _ _ (hST P)) (Ideal.mul_mem_left _ _ h))
    rw [← hd.mem_locP_L P y]
    exact ⟨fun h => localization_le_of_smul_mem hn hbar h, fun h => localization_le_of_smul_mem (one_notMem P.1) (fun x hx => by
      rw [one_smul]; exact Submodule.mem_sup_left hx) h⟩

theorem companion : ∀ (X : Fields) (b : ℕ) (SG : Finset (HeightOneSpectrum (𝓞 X.E))) (ϖ : 𝓞 X.E) (d : DecoSet (E := X.E) (n := b) (ST := divs ϖ) (SG := SG)), X.Ok → ϖ ≠ 0 → IsCoprime ϖ (X.conjO ϖ) → (∀ P ∈ divs ϖ, ϖ ∉ P.asIdeal ^ 2) → ∃ N'' : Submodule (𝓞 X.E) (Sp X.E b), IsSdLat N'' ∧ (∀ y ∈ d.1.N, (ϖ : X.E) • y ∈ N'') ∧ (∀ y ∈ N'', star (ϖ : X.E) • y ∈ d.1.N) ∧ ∀ (P : ↥(divs ϖ)) (y : Sp X.E b), y ∈ localization₂ P.1.asIdeal N'' ↔ y ∈ d.1.at P.1 ∧ d.1.f P y = 0 :=
  fun _ _ _ ϖ d _ h0 hcop _ => companion_gen ϖ d (fun P => (mem_divs h0 P.1).1 P.2) hcop

end GlobalTheory.MomT.MomentCompanion
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.JetMomentsOfUnitPeriod

section

@[expose] public section

open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.MomT

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable


open Formalism.MainNotions.TaylorLogMetric in
theorem jetMoments_of_unitPeriod
    (hM : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : IdE D → ℂ), IsCurveIdeal D cc →
      IsDiscriminantTwelfthRootOfIdealLattice D cc δ → IsChi D χ → ∀ (p : ℕ) [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]), p ≠ 2 →
      jacobiSym (-(D.host.d : ℤ)) p = 1 → Nat.Coprime (Ideal.absNorm cc) p →
      ∃ Ω : ℂ_[p], ‖Ω‖ = 1 ∧ GlobalTheory.MomT.MomentsAt D cc δ (B.eNat χ) lam Ω)
    (hE : MovesAll) (hL : LatticeFactsAll) : JetMoments := by
  intro D hD H s cc δ B χ cD ⟨hs, _, hcc, hδ, hχ, hcD⟩ u _ hcop w ι hw
  classical
  obtain ⟨lam, hlam⟩ := (_root_.GlobalTheory.MomPlace.places D.X.K (D.Pr.T u) s.σ₀ ι).1
  obtain ⟨⟨hTs, hTq⟩, -⟩ : (D.Pr.T u ∉ H.host.small ∧ D.Pr.T u ≠ H.host.q) ∧
      ∀ i, D.Pr.g i ∉ H.host.small ∧ D.Pr.g i ≠ H.host.q :=
    ⟨(_root_.GlobalTheory.AAUnitAway.locP_AA_and_primes_ne.2 D H s hD).1 u, (_root_.GlobalTheory.AAUnitAway.locP_AA_and_primes_ne.2 D H s hD).2⟩
  have hT2 : D.Pr.T u ≠ 2 := UpperTheory.Small.ne_two H.host hTs
  have hP := hD.primes
  have hp := hP.T_prime u
  have hn := hP.piT_norm u
  obtain ⟨Ω, hΩ, hmom⟩ := hM H cc δ B χ hcc hδ hχ (D.Pr.T u) lam hT2
    ((_root_.GlobalTheory.MomT.SplitK.splitk H D.X s (D.Pr.piT u) _ hs (hP.piT_Kq u)).2 hp hT2 hn (hP.piT_cop u)) hcop
  obtain ⟨M, _, hMe, hMs⟩ := hcD
  have hcQ : ∀ τ, cD τ ∈ TaylorLogMetric.Qbar := by
    intro τ
    obtain ⟨x, hx, -⟩ := hMs τ
    rw [← hx]
    exact mem_algebraicClosure_iff.2
      ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom (algebraMap M ℂ).toRatAlgHom)
  refine ⟨fun τ => TaylorLogMetric.lamC lam (cD (s.iT τ)) / Ω, fun τ => ?_, ?_⟩
  · obtain ⟨x, hx, hx'⟩ := hMs (s.iT τ)
    rw [norm_div, hΩ, div_one, ← hx]
    exact GlobalTheory.EigenGenerator.norm_generator_eq_one H _ lam hTs hTq M hMe _ x hx'
  intro sel S mu cst hsel hS hcq i b _ hb SG SG' d d' hd hd' Ξ₀ hΞ
  have hev : ∀ j, Even (D.R.N j) := fun j => D.R.k_even.add ((D.R.t_odd.add_one).mul_left j)
  have ha := hev i
  have hb' : Even b := hb ▸ hev _
  obtain ⟨hla, hsm⟩ := hL H D.X s cc δ B χ cD hD.fields hs hcc hδ hχ _ _ ha hb'
  have hπ0 : D.Pr.piT u ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hn
    exact hp.ne_zero (by exact_mod_cast hn.symm)
  have hπ0' : D.X.conjO (D.Pr.piT u) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hn
    exact hp.ne_zero (by exact_mod_cast hn.symm)
  obtain ⟨hfree, hrow⟩ := _root_.GlobalTheory.Proof.AbsNormSplitPlace.main D u sel S mu hD hsel (hS (Or.inr ⟨u, rfl⟩))
    (fun k => hS (Or.inl (by fin_cases k <;> simp)))
  have hUT : ∀ P : HeightOneSpectrum (𝓞 D.X.E), ((D.Pr.T u : ℕ) : 𝓞 D.X.E) ∈ P.asIdeal →
      localization₂ P.asIdeal (ambOf s B χ cD).AA = localization₂ P.asIdeal (1 : Submodule (𝓞 D.X.E) D.X.E) :=
    fun P h => _root_.GlobalTheory.AAUnitAway.locP_AA_and_primes_ne.1 H D.X s cc δ B χ cD P _ hp hTs hTq h hcop
  have hmemS : ∀ P, P ∈ Sall sel mu u ↔ D.Pr.piT u ∈ P.asIdeal ∨ P ∈ rowSG D.Pr sel mu := by
    intro P
    unfold Sall
    rw [Finset.mem_union, Primes.vT, mem_divs hπ0]
  have hU : (ambOf s B χ cD).AAUnit (Sall sel mu u) := by
    intro P hPS
    rcases (hmemS P).1 hPS with h | h
    · exact hUT P (hn ▸ Ideal.mul_mem_right _ _ h)
    · have bad := _root_.GlobalTheory.ThetaMove.BadPrimes.bad_primes D.X D.Pr sel S mu u hD.fields hP hsel (hS (Or.inr ⟨u, rfl⟩))
        (fun k => hS (Or.inl (by fin_cases k <;> simp))) P hPS
      exact _root_.GlobalTheory.PeriodIdealUnit.locP_AA_eq_one D.X H s cc δ B χ cD P bad.2.1 bad.2.2.1 (hcq P h)
  have hG : Nat.Coprime (∏ P : rowSG D.Pr sel mu, Formalism.L2.Col.qOf P.1) (D.Pr.T u) :=
    Nat.Coprime.prod_left fun P _ => (Nat.coprime_primes (hrow P.1 P.2).1 hp).2 (hrow P.1 P.2).2.1
  have hctx : Ctx (ambOf s B χ cD) (D.R.N i) b (Sall sel mu u) (rowSG D.Pr sel mu) (D.Pr.piT u) (D.Pr.T u)
      ((∏ P : rowSG D.Pr sel mu, Formalism.L2.Col.qOf P.1) ^ cst.B) (cAof sel mu cst) :=
    ⟨hD.fields, ⟨hla.1, hla.2.1, hfree, hU, hla.2.2.2.2⟩,
      fun P h => hUT P (hn ▸ Ideal.mul_mem_left _ _ ((mem_divs hπ0' P).1 h)), hsm, hp, hn, hP.piT_cop u, hmemS,
      fun P h => (hrow P h).2.2.1, hG.pow_left _, hG.pow_left _⟩
  have hN : IsSdLat d.1.N := ⟨d.2.lat, d.2.uni⟩
  have hN' : IsSdLat d'.1.N := ⟨d'.2.lat, d'.2.uni⟩
  obtain ⟨c1, c1'⟩ := _root_.GlobalTheory.MomT.ChiUnit.chi_det_unit H D.X s χ _ lam (D.Pr.piT u) _ d.1.N hD.fields hs hχ hn hN
    fun P h => hd ⟨P, (mem_divs hπ0 P).2 h⟩
  obtain ⟨c2, c2'⟩ := _root_.GlobalTheory.MomT.ChiUnit.chi_det_unit H D.X s χ _ lam (D.Pr.piT u) _ d'.1.N hD.fields hs hχ hn hN'
    fun P h => hd' ⟨P, (mem_divs hπ0 P).2 h⟩
  have hF : (ambOf s B χ cD).chiF (D.R.N i) b d.1.N d'.1.N ∈ TaylorLogMetric.Qbar := mul_mem (zpow_mem c1 _) (zpow_mem c2 _)
  have hF1 : ‖TaylorLogMetric.lamC lam ((ambOf s B χ cD).chiF (D.R.N i) b d.1.N d'.1.N)‖ = 1 := by
    refine (congrArg norm (lamC_mul lam (zpow_mem c1 _) (zpow_mem c2 _))).trans ?_
    rw [lamC_zpow lam c1, lamC_zpow lam c2, norm_mul, norm_zpow, norm_zpow, c1', c2', one_zpow, one_zpow, one_mul]
  refine ⟨fun hseen => ?_, fun hseen => ?_⟩
  · refine type_bar hctx hlam hw d d' hF hF1 Ξ₀ hΞ ?_
    have := _root_.GlobalTheory.MomT.PtMoments.ptMom H D.X s cc δ B χ cD _ lam ι Ω (D.X.conjO (D.Pr.piT u)) (D.R.N i) b hD.fields hs hcc hT2 hcop
      (fun k => (hlam k).2) hcQ (fun τ τ' => ?_) (by rw [conjO_conjO, mul_comm, hn])
      (by rw [conjO_conjO]; exact (hP.piT_cop u).symm) (fun τ => (hw _).1 (hseen τ)) ha hb' hla hsm hmom
    · have e : ((D.X.conjO (D.Pr.piT u) : 𝓞 D.X.E) : D.X.E) = star ((D.Pr.piT u : 𝓞 D.X.E) : D.X.E) := rfl
      rwa [e, star_star] at this
    · have e : ((D.X.conjO (D.Pr.piT u) : 𝓞 D.X.E) : D.X.E) = star ((D.Pr.piT u : 𝓞 D.X.E) : D.X.E) := rfl
      rw [e, hD.fields.emb_star, hD.fields.emb_star, hP.piT_Kq u τ τ']
  · have hsq : ∀ P ∈ divs (D.Pr.piT u), D.Pr.piT u ∉ P.asIdeal ^ 2 := by
      intro P hPm h2
      refine GlobalTheory.SplitUnram.natCast_notMem_sq D.X.E D.X.conjO (D.Pr.piT u) _ conjO_conjO hp hn (hP.piT_cop u) ?_
        (hP.vT_norm u) P hPm (hn ▸ Ideal.mul_mem_right _ _ h2)
      have h1 : (divs (D.Pr.piT u)).card = Module.finrank ℚ D.X.F := (hP.vT_card u).trans hD.fields.card_Tau
      rw [h1, ← Module.finrank_mul_finrank ℚ D.X.F D.X.E, hD.fields.rankE, mul_comm]
    obtain ⟨N'', hN'', hc⟩ := _root_.GlobalTheory.MomT.MomentCompanion.companion D.X b SG' (D.Pr.piT u) d' hD.fields hπ0 (hP.piT_cop u) hsq
    have hval := _root_.GlobalTheory.MomT.ChiMove.chi_move H D.X s χ b SG' (D.Pr.piT u) d' N'' hD.fields hs hχ hπ0 (hP.piT_cop u) hsq hN'' hc
    set k : D.X.K := ∏ τ, (D.X.emb τ (((D.Pr.piT u : 𝓞 D.X.E) : D.X.E) / star ((D.Pr.piT u : 𝓞 D.X.E) : D.X.E)))⁻¹ with hk
    have hval' : χ (TaylorLogMetric.detId H (s.lat d'.1.N) (s.lat N'')) = s.σ₀ k := by
      rw [hval, hk, map_prod]
      exact Finset.prod_congr rfl fun τ _ => (map_inv₀ _ _).symm
    have hk0 : k ≠ 0 := by
      have h0 : ((D.Pr.piT u : 𝓞 D.X.E) : D.X.E) ≠ 0 := by exact_mod_cast hπ0
      exact Finset.prod_ne_zero_iff.2 fun τ _ => inv_ne_zero ((map_ne_zero _).2 (div_ne_zero h0 (star_ne_zero.2 h0)))
    have hkn : ‖ι k‖ ≤ (D.Pr.T u : ℝ) ^ D.X.f := by
      rw [hk, map_prod, norm_prod]
      refine (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun τ _ => ?_).trans_eq
        (Finset.prod_const (D.Pr.T u : ℝ))
      rw [map_inv₀]
      exact norm_ratio_le (ι.comp (D.X.emb τ)) hn
    have hcard : (divs (D.Pr.piT u)).card = D.X.f := hP.vT_card u
    have key := type_p hctx hlam hw d d' hd hF hF1 Ξ₀ hΞ
      (_root_.GlobalTheory.MomT.PtMoments.ptMom H D.X s cc δ B χ cD _ lam ι Ω (D.Pr.piT u) (D.R.N i) b hD.fields hs hcc hT2 hcop
        (fun k => (hlam k).2) hcQ (hP.piT_Kq u) hn (hP.piT_cop u) (fun τ => (hw _).1 (hseen τ)) ha hb' hla hsm hmom)
      (hP.vT_norm u) N'' hN'' hc (s.σ₀ (k ^ (D.R.N i / 2))) (hlam _).1 ?_ ?_
    · rw [hcard] at key
      exact key
    · rw [(hlam _).2, map_pow, norm_pow, ← pow_mul, Nat.div_two_mul_two_of_even ha, hcard, pow_mul]
      exact pow_le_pow_left₀ (norm_nonneg _) hkn _
    · intro R hR z
      have hmv := _root_.GlobalTheory.MomT.Move.move H D.X s cc δ B χ cD _ b d.1.N d'.1.N N'' hD.fields hs (hE H cc δ B χ hcc hδ hχ) ha hb' hla
        hN hN' hN'' R hR z
      have hR0 : ((Real.sqrt (R.card : ℝ) : ℝ) : ℂ) ≠ 0 := by
        obtain ⟨x, hx, -⟩ := hR.2.2 0 (zero_mem _)
        have : (0 : ℝ) < R.card := by exact_mod_cast Finset.card_pos.2 ⟨x, hx⟩
        exact_mod_cast (Real.sqrt_pos.2 this).ne'
      have hσ : s.σ₀ k ≠ 0 := (map_ne_zero _).2 hk0
      rw [hmv, hval', map_pow, zpow_neg, zpow_natCast]
      field_simp

end GlobalTheory.MomT
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LatticeFactsAll

section

@[expose] public section

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN
open IsDedekindDomain Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Th1.H GlobalTheory.ThetaMove GlobalTheory.ThetaMove.SeamMoves Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

noncomputable section

namespace GlobalTheory.MomLat

theorem latticeFactsAll : GlobalTheory.MomT.LatticeFactsAll := by
  intro D X s cc δ B χ cD hX hs hcc hδ hχ a b ha hb
  have hL := GlobalTheory.ThetaMove.LatticeFacts.latAll B hcc hδ
  have hVm := B.vec_mem_ne hcc hδ (delta_ne_zero B) (B.stdOK hcc hδ) χ hχ
  obtain ⟨hsd, hlam⟩ := GlobalTheory.PeriodTransport.seam_lattices X D s cc δ B χ cD hs
  have hq := qIntAll_of_latAll D cc δ B hL
  have hadm : ∀ (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)), IsSdLat N → IsSdLat N' →
      TaylorLogMetric.admitted D a b (s.lat N) (s.lat N') := fun N N' h h' => ⟨ha, hb, hsd _ _ h, hsd _ _ h'⟩
  refine ⟨⟨delta_ne_zero B, Fintype.card_pos_iff.1 hX.f_pos, by simp, fun P hP => absurd hP (Finset.notMem_empty P),
    aa_fg s B χ cD, fun N N' h h' => ?_⟩, fun N N' h h' k => ?_⟩
  · obtain ⟨h1, h2, h3⟩ := (Transport.inter_transport _ _ (reidx s a b) (Formalism.L2.Ker.HV (ambOf s B χ cD).sc)
      (formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau a b) (alV (ambOf s B χ cD).d (ambOf s B χ cD).sc) (TaylorLogMetric.al D B.tor)
      (lam (ambOf s B χ cD) N N') (lam (ambOf s B χ cD) N N') (TaylorLogMetric.La D B.tor (s.lat N) (s.lat N'))
      (TaylorLogMetric.La D B.tor (s.lat N) (s.lat N')) 0 (form_reidx s _ a b) (hlam a b N N') (hlam a b N N')
      (fun x hx => by
        obtain ⟨m, hm⟩ := hq a b _ _ (hadm N N' h h') (reidx s a b x) ((hlam a b N N' x).1 hx)
        exact alV_eq s B x hm)
      (isHerm_formV _ _ _ _) (hL.1 a b _ _ (hadm N N' h h')).1 (hL.1 a b _ _ (hadm N N' h h')).2).1
    exact ⟨h3 (B.eNat χ a b (s.lat N) (s.lat N')) (hVm a b _ _ (hadm N N' h h')).1.2, h1, h2⟩
  · have hd : ContDiff ℂ (k : WithTop ℕ∞) (B.eNat χ a b (s.lat N) (s.lat N')) :=
      GlobalTheory.SCV.contDiff_of_differentiable (hVm a b _ _ (hadm N N' h h')).1.1 _
    exact hd.comp (reidx s a b).toLinearMap.toContinuousLinearMap.contDiff

end GlobalTheory.MomLat
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.KernelJetsLevelPlaceIntegralMoments

section

@[expose] public section

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN

namespace GlobalTheory.MomTop

theorem jetMoments : GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable.JetMoments :=
  GlobalTheory.MomT.jetMoments_of_unitPeriod
    (GlobalTheory.T.unitPeriodTranslates_moments_finite GlobalTheory.MomEq.eq_and_alg.1 GlobalTheory.MomEq.eq_and_alg.2)
    GlobalTheory.MomEq.eq_and_alg.1 GlobalTheory.MomLat.latticeFactsAll

end GlobalTheory.MomTop
end
end
