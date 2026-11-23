module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.TaylorWilesObstructionBound
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.ExistsAdjoinCoeffCharacterSubMemMaximalIdealPow
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ChebotarevFamilies.IpEq
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ChebotarevFamilies.UnipPow
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.CoefficientExtensionPreservesConditionsAndDet
public import Mathlib.RingTheory.PowerSeries.Basic
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
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
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PairedDualFirstOrderDualMatrixSpace
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.RepAlg
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.FieldTheory.Finite.Basic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PairedDualFirstOrderDualMatrixSpace
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.DiscStIff
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ThetaCoefficientMapEq
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.TypeIDisc
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.ConstMap

section

@[expose] public section

open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

theorem UpperTheory.V.Pa.Det.constMap :
    ∀ {K K' : Type} [Field K] [Finite K] [Field K'] (j : PowerSeries K →+* PowerSeries K'), ∃ ι : K →+* K', ∀ a, j (PowerSeries.C a) = PowerSeries.C (ι a) := by
  intro K K' _ _ _ j
  classical
  haveI := Fintype.ofFinite K
  set p := ringChar K with hpdef
  haveI : CharP K p := ringChar.charP K
  obtain ⟨n, hp, hq⟩ := FiniteField.card K p
  haveI : Fact p.Prime := ⟨hp⟩
  set e : K →+* PowerSeries K' := j.comp PowerSeries.C
  haveI : CharP (PowerSeries K') p := charP_of_injective_ringHom e.injective p
  have key : ∀ f : PowerSeries K', f ^ (p ^ (n : ℕ)) = f → f = PowerSeries.C (PowerSeries.constantCoeff f) := by
    intro f hf
    set c := PowerSeries.constantCoeff f with hcdef
    have hc : c ^ (p ^ (n : ℕ)) = c := by
      have h2 := congrArg PowerSeries.constantCoeff hf
      rw [map_pow] at h2
      exact h2
    have hd : (f - PowerSeries.C c) ^ (p ^ (n : ℕ)) = f - PowerSeries.C c := by
      rw [sub_pow_char_pow, hf, ← map_pow, hc]
    have hd0 : PowerSeries.constantCoeff (f - PowerSeries.C c) = 0 := by
      rw [map_sub, PowerSeries.constantCoeff_C, hcdef, sub_self]
    have hq1 : 1 ≤ p ^ (n : ℕ) - 1 := by
      have h1 : 2 ≤ p := hp.two_le
      have h3 : p ≤ p ^ (n : ℕ) := Nat.le_self_pow (PNat.ne_zero n) p
      omega
    have hprod : (f - PowerSeries.C c) * ((f - PowerSeries.C c) ^ (p ^ (n : ℕ) - 1) - 1) = 0 := by
      rw [mul_sub, mul_one, ← pow_succ', Nat.sub_add_cancel (by omega), hd, sub_self]
    rcases mul_eq_zero.mp hprod with h | h
    · exact sub_eq_zero.mp h
    · exfalso
      have h4 := congrArg PowerSeries.constantCoeff h
      rw [map_sub, map_pow, hd0, zero_pow (by omega), map_one, map_zero] at h4
      exact zero_ne_one (sub_eq_zero.mp h4)
  refine ⟨PowerSeries.constantCoeff.comp e, fun a => ?_⟩
  have ha : j (PowerSeries.C a) ^ (p ^ (n : ℕ)) = j (PowerSeries.C a) := by
    rw [← map_pow, ← map_pow, ← hq, FiniteField.pow_card]
  exact key _ ha
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.StableIff

section

@[expose] public section

open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

theorem UpperTheory.V.Pa.Det.stableIff :
    ∀ {l : ℕ} [Fact l.Prime] {F : GFrame l} {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] {n : ℕ} {r : Resid F O n} (B : UniversalOrdinaryDeterminantRing r) (q : PrimeSpectrum B.B), B.IsStable q ↔ DiscSt B.u.D q.asIdeal := by
  intro l _ F O _ _ _ n r B q
  have hk : RingHom.ker (B.toKap q) = q.asIdeal := by
    rw [UniversalOrdinaryDeterminantRing.toKap, RingHom.ker_comp_of_injective _
      (algebraMap q.asIdeal.ResidueField (B.kap q)).injective,
      Ideal.ker_algebraMap_residueField]
  rw [← hk, Det.discStIff]
  rfl
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.ThickNonSS

section

@[expose] public section

open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

theorem UpperTheory.V.Pa.Det.thickNonSS :
    ∀ {l : ℕ} [Fact l.Prime] {F : GFrame l} {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] {n : ℕ} {r : Resid F O n} (B : UniversalOrdinaryDeterminantRing r) (q : PrimeSpectrum B.B), B.IsThick q → NonSS (augmentationIdealKernel B.u) (RingHom.id B.B) q.asIdeal := by
  intro l _ F O _ _ _ n r B q h
  have he : augmentationIdealKernel B.u = (B.GroupAlgebraKernelIdeal : Set (MonoidAlgebra B.B F.G₀)) := by
    have : B.u.D.chBar (pairGens B.u) = B.GroupAlgebraKernelIdeal := by
      unfold UniversalOrdinaryDeterminantRing.GroupAlgebraKernelIdeal UniversalOrdinaryDeterminantRing.E0gens GDet.chBar pairGens
      rw [Set.union_assoc]
    unfold augmentationIdealKernel
    rw [this]
    rfl
  refine ⟨B.kap q, inferInstance, B.toKap q, ?_, ?_⟩
  · ext x
    unfold UniversalOrdinaryDeterminantRing.toKap
    rw [RingHom.mem_ker, RingHom.comp_apply, map_eq_zero, Ideal.algebraMap_residueField_eq_zero]
  · rw [RingHom.comp_id, he]
    exact h.2
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ChebotarevFamilies.PFromAutOf

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

namespace UpperTheory.V.Pa

private theorem chi_ofRep {n : ℕ} {A G : Type} [CommRing A] [Group G] (ρ : G →* Matrix (Fin n) (Fin n) A) (g : G) :
    (GDet.ofRep ρ).chi (MonoidAlgebra.single g 1) = (ρ g).charpoly := by
  change (GDet.repAlg ρ (Polynomial A) _).det = _
  rw [map_sub, MonoidAlgebra.mapRingHom_single, Matrix.charpoly]
  congr 1
  ext i j : 2
  by_cases h : i = j <;> simp [GDet.repAlg, Matrix.charmatrix, h, Matrix.one_apply, Matrix.diagonal_apply]

private theorem map_ofRep {n : ℕ} {A B G : Type} [CommRing A] [CommRing B] [Group G] (ρ : G →* Matrix (Fin n) (Fin n) A)
    (f : A →+* B) : (GDet.ofRep ρ).map f = GDet.ofRep (f.mapMatrix.toMonoidHom.comp ρ) := by
  refine GDet.ext fun C _ _ x => ?_
  letI : Algebra A C := ((algebraMap B C).comp f).toAlgebra
  change (GDet.repAlg ρ C x).det = (GDet.repAlg _ C x).det
  congr 2

theorem chain_of (hN : Norm) (hC : Choice) (hP : ArPl) (h1 : FirstOrderDualArithmeticBound) (h2 : TaylorWilesObstructionBound) (hR : Raw) (P : CohP)
    (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (s : HidaSetting l L Ω) (V0 : s.Lev) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O]
    [Algebra ℤ_[l] O] (n : ℕ) (r : Resid V0.frame O n) (B : UniversalOrdinaryDeterminantRing r) (J : Ideal B.B) (hn : 0 < n) (hS : V0.S' = s.S)
    (hL : LocCFT s) (hμ : ∃ g : V0.frame.G₀, PadicInt.toZMod ((V0.frame.ε g : ℤ_[l]ˣ) : ℤ_[l]) ≠ 1) (hA : HasAut B J)
    (h : ℕ) (x : Fin (h + 1) → Point r) (f : ∀ i, B.B →ₐ[O] (x i).A) (hx : ∀ i, (x i).NiceI ∨ (x i).NiceE)
    (hf : ∀ i, B.IsPt (x i) (f i)) :
    ChainConcl (pairOf B.u) J (fun i => RingHom.ker (f i)) ∧
      ∀ i, (x i).TypeI → ∀ q : Ideal B.B, q ≤ RingHom.ker (f i) → DiscSt B.u.D q := by
  haveI := IsCoef.char (l := l) (O := O)
  haveI := IsCoef.finite (l := l) (O := O)
  haveI := IsCoef.complete (l := l) (O := O)
  obtain ⟨hΦ, hT⟩ := hP P l L Ω s V0 O n r hS
  have hI := (ipEq l L Ω s V0 O n r).1
  choose y j jinj jloc _ jD jψ y3 y4 yI using fun i => hN l V0.frame O n r (x i) (globOf r V0).frame.Iu s.odd hn
    (fun u => ((hI u).2.symm.trans (hI u).1).le) (hx i)
  obtain ⟨q, sg, z, j', k, al, hsg, hE, hcard, hdet, heig⟩ := hC l (globOf r V0).frame n h y s.odd hΦ hμ y3
  obtain ⟨T, ⟨Pl⟩, rfl, hTs⟩ := hT q sg hsg
  obtain rfl : T.sg = sg := funext hTs
  obtain ⟨A⟩ := hA T Pl
  choose ι hι using fun i => Det.constMap ((j' i).comp (j i))
  have hD : ∀ i, GDet.ofRep (mat (z i).ρ) = (GDet.ofRep (mat (x i).ρ)).map ((j' i).comp (j i)) := fun i => by
    exact (Det.coefficientExtension_preserves_conditions_and_det _ _ _ (hE i)).2.2.trans (congrArg (·.map (j' i)) (jD i))
  have hker : ∀ i, ∀ g : V0.frame.G₀, (g : V0.frame.Γ) ∈ PL l T.H.toSubgroup → (z i).ρ g = 1 := fun i => by
    refine rhoPL l (globOf r V0).frame n (z i) T.H fun g hg => ?_
    obtain ⟨e1, e2, -⟩ := (Pl.H_eq g).1 hg
    refine ⟨e1, ?_⟩
    have hcc : (PowerSeries.constantCoeff : (z i).A →+* (z i).K).comp ((j' i).comp (j i)) =
        (ι i).comp PowerSeries.constantCoeff := RingHom.ext fun a => by
      haveI := jloc i
      haveI := (hE i).2.1
      have m1 : ¬ IsUnit (a - PowerSeries.C (PowerSeries.constantCoeff a)) := by
        simp [PowerSeries.isUnit_iff_constantCoeff]
      have m2 : ¬ IsUnit (j' i (j i (a - PowerSeries.C (PowerSeries.constantCoeff a)))) := fun u =>
        m1 (IsLocalHom.map_nonunit _ (IsLocalHom.map_nonunit _ u))
      rw [PowerSeries.isUnit_iff_constantCoeff, isUnit_iff_ne_zero, not_not, map_sub, map_sub, map_sub, sub_eq_zero] at m2
      have m3 := congrArg PowerSeries.constantCoeff (hι i (PowerSeries.constantCoeff a))
      exact m2.trans (m3.trans (PowerSeries.constantCoeff_C _))
    have e3 : (GDet.ofRep (mat (z i).ρ)).map (PowerSeries.constantCoeff : (z i).A →+* (z i).K) =
        r.Dbar.map ((ι i).comp (algebraMap (ResidueField O) (x i).K)) := by
      rw [hD i]
      refine Eq.trans (b := (GDet.ofRep (mat (x i).ρ)).map ((ι i).comp PowerSeries.constantCoeff)) (by rw [← hcc]; rfl) ?_
      exact congrArg (·.map (ι i)) (x i).red
    rw [map_ofRep, Resid.Dbar, map_ofRep] at e3
    have e4 := congrArg (·.chi (MonoidAlgebra.single ⟨g, e1⟩ 1)) e3
    simp only [chi_ofRep] at e4
    refine e4.trans ?_
    have e5 : W.diagRep r.chib ⟨g, e1⟩ = 1 := by
      change Matrix.diagonal _ = _
      simp only [e2, Units.val_one, Matrix.diagonal_one]
    refine (chi_ofRep _ _).trans ?_
    change ((RingHom.mapMatrix ((ι i).comp (algebraMap (ResidueField O) (x i).K))) (W.diagRep r.chib ⟨g, e1⟩)).charpoly = _
    rw [e5, map_one, Matrix.charpoly_one, Fintype.card_fin]
  let pt : ∀ i, Pt T (pairOf B.u) (n * Module.finrank ℚ (Lp L) + n * T.q) := fun i =>
    letI : Algebra O (z i).K := ((ι i).comp (algebraMap O (x i).K)).toAlgebra
    { x := z i
      k := k i
      al := al i
      eig := heig i
      b1 := h1 P l L Ω s V0 O n r T Pl (z i) (k i) (al i) hS hL hμ (hker i)
        ((Det.coefficientExtension_preserves_conditions_and_det _ _ _ (hE i)).1 _ (y4 i)) (heig i) (hdet i)
      b2 := h2 P l L Ω s V0 O n r T Pl (z i) (k i) (al i) hS hμ (hker i) (heig i)
      f := { ((j' i).comp (j i)).comp (f i : B.B →+* (x i).A) with
        commutes' := fun a => by
          change ((j' i).comp (j i)) (f i (algebraMap O B.B a)) = _
          rw [AlgHom.commutes]
          rw [PowerSeries.algebraMap_apply, PowerSeries.algebraMap_apply]
          exact hι i _ }
      maps := ⟨by rw [hD i, ← (hf i).1]; rfl, fun v a => by
        rw [(hE i).2.2.2.2.2 v a, jψ i v a, ← (hf i).2 v a]; rfl⟩ }
  have hk : ∀ i, RingHom.ker (pt i).f = RingHom.ker (f i) := fun i => by
    ext b
    change j' i (j i (f i b)) = 0 ↔ f i b = 0
    rw [map_eq_zero_iff _ (hE i).1, map_eq_zero_iff _ (jinj i)]
  refine ⟨?_, fun i hi q hq => ?_⟩
  · have := hR l _ (globOf r V0) T n O (residOf r) B.B (pairOf B.u) J _ A s.odd
      ⟨fun g hg a => ((Pl.H_eq g).1 hg).2.1 a, fun u => (hI u).2⟩
      (fun N b => by
        obtain ⟨c, hc, hb⟩ := CA.exists_adjoin_coeff_character_sub_mem_maximalIdeal_pow r B N b
        refine ⟨c, Algebra.adjoin_mono ?_ hc, hb⟩
        rintro _ (⟨a, g, -, -, rfl⟩ | e)
        · exact Or.inl ⟨a, g, rfl⟩
        · exact Or.inr e) h pt hcard
    simpa only [hk] using this
  · exact Det.typeIDisc (z i) B.u.D (((j' i).comp (j i)).comp (f i : B.B →+* (x i).A)) ((hE i).2.2.2.2.1.trans (yI i hi)) (pt i).maps.1 q (hq.trans (hk i).ge)

theorem pFromAut_of (hN : Norm) (hC : Choice) (hP : ArPl) (h1 : FirstOrderDualArithmeticBound) (h2 : TaylorWilesObstructionBound) (hR : Raw) : PfromAut := by
  intro P l _ L Ω _ _ _ _ _ _ s V0 O _ _ _ _ _ n r B J hn hS hL hμ hA
  have key := chain_of hN hC hP h1 h2 hR P l L Ω s V0 O n r B J hn hS hL hμ hA
  have hE : augmentationIdealKernel (pairOf B.u) = augmentationIdealKernel B.u := by
    rw [(ipEq l L Ω s V0 O n r).2 B]
    ext z
    simp only [augmentationIdealKernel, UniversalOrdinaryDeterminantRing.GroupAlgebraKernelIdeal, GDet.chBar, pairGens, UniversalOrdinaryDeterminantRing.E0gens, Set.mem_setOf_eq, Set.union_assoc]
  refine ⟨fun x f hx hf hJ q hq => ?_, fun h x f e hx hf he h₁ q hq hs => ?_⟩
  · obtain ⟨k1, k2⟩ := key 0 (fun _ => x) (fun _ => f) (fun _ => Or.inl hx) fun _ => hf
    exact k1 Fin.elim0 (fun i => i.elim0) ⟨_, RingHom.ker_isPrime f, k2 0 hx.2.1 _ le_rfl, hJ, le_rfl⟩ q.asIdeal q.isPrime hq
      (Or.inl (k2 0 hx.2.1 _ hq))
  · obtain ⟨k1, -⟩ := key h x f (fun i => Or.inr (hx i)) hf
    obtain ⟨q₁, a1, a2, a3⟩ := h₁
    refine k1 (fun i => (e i).asIdeal) (fun i => ⟨(e i).isPrime, hE ▸ Det.thickNonSS B _ (he i).1, (he i).2⟩)
      ⟨_, q₁.isPrime, (Det.stableIff B _).1 a1, a2, a3⟩ q.asIdeal q.isPrime hq ?_
    exact hs.imp (Det.stableIff B _).1 fun t => hE ▸ Det.thickNonSS B _ t

end UpperTheory.V.Pa
end
end
