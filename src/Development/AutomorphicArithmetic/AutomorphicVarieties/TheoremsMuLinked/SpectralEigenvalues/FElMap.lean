module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.OrdinaryHeckeAlgebraIntegral
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DGmap
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.LevelModule
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoEvLow
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoMvps
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.OrdinaryHeckeAlgebraIntegral
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.SpectralEigenvalues.BetaSurj
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.SpectralEigenvalues.GenAll
import Mathlib.Tactic.ReduceModChar
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.SpectralEigenvalues.ImportsTer
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.SpectralEigenvalues.RepSingle
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.SpectralEigenvalues.BetaLam

section

@[expose] public section

open IsLocalRing Matrix Filter UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.Lev UpperTheory.V.AlgebraTools UpperTheory.V.Th
open scoped TensorProduct

theorem UpperTheory.V.Th.Sp.betaLam :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 G : Glob l L) (h : G.Hom G0) (n : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (r : Resid G0.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (J : Ideal B) (D : ℕ) (b : TWBase u J Empty D) (q N : ℕ) (A : OpMod b h q N), ∀ a : abelian₂ O Empty D, A.β (algebraMap (abelian₂ O Empty D) A.R a) = b.lam a := by
  intro l _ L G0 G h n O _ _ _ _ _ r B _ _ _ u J D b q N A a
  haveI hOO : IsCO O O :=
    { complete := IsCoef.complete
      isLocalHom := ⟨fun x hx => by simpa using hx⟩
      res_surj := fun x => ⟨x, by simp⟩ }
  haveI hL : IsCO O (abelian₂ O Empty D) := co_mvps O O (Empty ⊕ Fin D)
  have hmax : ∀ s : Empty ⊕ Fin D, b.lam (MvPowerSeries.X s) ∈ maximalIdeal B := by
    intro s
    rw [← res_eq_zero_iff O B, res_map, res_eq_zero_iff, IsLocalRing.mem_maximalIdeal,
      mem_nonunits_iff]
    intro hu
    have h0 := hu.map MvPowerSeries.constantCoeff
    simp at h0
  obtain ⟨F, _, huniq⟩ :=
    co_ev O O B (Empty ⊕ Fin D) (Algebra.ofId O B) (fun s => b.lam (MvPowerSeries.X s)) hmax
  let F1 : abelian₂ O Empty D →ₐ[O] B :=
    A.β.comp (IsScalarTower.toAlgHom O (abelian₂ O Empty D) A.R)
  have e1 : F1 = F := by
    apply huniq
    refine ⟨fun x => ?_, fun s => ?_⟩
    · rw [MvPowerSeries.c_eq_algebraMap]
      exact F1.commutes x
    · rcases s with e | k
      · exact e.elim
      · show A.β (algebraMap (abelian₂ O Empty D) A.R (MvPowerSeries.X (Sum.inr k))) = _
        rw [A.segmentWeightExponent k, b.segmentWeightExponent k, map_sub, map_mul, map_one, AlgHom.commutes]
        congr 2
        have hp := congrArg (fun χ => ((χ (b.wt.γ k) : Bˣ) : B)) (A.β_pair.2 (b.wt.v k) (b.wt.i k))
        simpa [pushCh] using hp
  have e2 : b.lam = F := by
    apply huniq
    refine ⟨fun x => ?_, fun s => rfl⟩
    rw [MvPowerSeries.c_eq_algebraMap]
    exact b.lam.commutes x
  have := congrArg (fun φ : abelian₂ O Empty D →ₐ[O] B => φ a) (e1.trans e2.symm)
  simpa [F1] using this
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.SpectralEigenvalues.ImportsFurther

section

@[expose] public section

open IsLocalRing Matrix Filter UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.Lev UpperTheory.V.AlgebraTools UpperTheory.V.Th
open scoped TensorProduct

theorem UpperTheory.V.Th.Sp.trans :
    ∀ (R M W : Type) [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup W] [Module R W] (q n : ℕ) (act1 : PUY R q n →ₐ[R] Module.End R M) (actw : PU R q n →ₐ[R] Module.End R W) (tr : M →ₗ[R] W), Function.Surjective tr → LinearMap.ker tr = ⨆ p : Fin q × Fin n, LinearMap.range (act1 (yV R p.1 p.2)) → (∀ j i m, tr (act1 (uV R j i) m) = actw (MvPolynomial.X (j, i)) (tr m)) → (∀ τ m, tr (act1 τ m) = actw (MvPolynomial.aeval (Sum.elim MvPolynomial.X 0) τ) (tr m)) ∧ ∀ (I : Ideal R) m, tr m ∈ (I • ⊤ : Submodule R W) → m ∈ (I • ⊤ : Submodule R M) ⊔ ⨆ p : Fin q × Fin n, LinearMap.range (act1 (yV R p.1 p.2)) := by
  intro R M W _ _ _ _ _ q n act1 actw tr hsurj hker hu
  have hy : ∀ p : Fin q × Fin n, ∀ m, tr (act1 (yV R p.1 p.2) m) = 0 := by
    intro p m
    rw [← LinearMap.mem_ker, hker]
    exact Submodule.mem_iSup_of_mem p (LinearMap.mem_range_self _ m)
  refine ⟨fun τ => ?_, fun I m hm => ?_⟩
  · induction τ using MvPolynomial.induction_on with
    | C a =>
        intro m
        rw [MvPolynomial.aeval_C, ← MvPolynomial.algebraMap_eq, AlgHom.commutes, AlgHom.commutes]
        simp
    | add p r hp hr =>
        intro m
        simp [map_add (f := _), hp, hr]
    | mul_X p s hp =>
        intro m
        rcases s with ⟨j, i⟩ | ⟨j, i⟩
        · rw [map_mul, Module.End.mul_apply, hp, map_mul, map_mul, Module.End.mul_apply,
            MvPolynomial.aeval_X, Sum.elim_inl]
          exact congrArg _ (hu j i m)
        · rw [map_mul, Module.End.mul_apply, hp, map_mul, MvPolynomial.aeval_X, Sum.elim_inr,
            show tr (act1 (MvPolynomial.X (Sum.inr (j, i))) m) = 0 from hy (j, i) m]
          simp
  · have htop : (I • ⊤ : Submodule R W) = (I • ⊤ : Submodule R M).map tr := by
      rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr hsurj]
    rw [htop] at hm
    obtain ⟨m', hm', he⟩ := hm
    have hk : m - m' ∈ ⨆ p : Fin q × Fin n, LinearMap.range (act1 (yV R p.1 p.2)) := by
      rw [← hker, LinearMap.mem_ker, map_sub, he, sub_self]
    have hmm : m = m' + (m - m') := by abel
    rw [hmm]
    exact Submodule.add_mem_sup hm' hk
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.SpectralEigenvalues.LamW

section

@[expose] public section

open IsLocalRing Matrix Filter UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.Lev UpperTheory.V.AlgebraTools UpperTheory.V.Th
open scoped TensorProduct

theorem UpperTheory.V.Th.Sp.lamW :
    ∀ (O R B M V : Type) [CommRing O] [CommRing R] [CommRing B] [Algebra O R] [Algebra O B] [AddCommGroup M] [Module B M] [AddCommGroup V] [Module R V] (q n : ℕ) (β : R →ₐ[O] B) (x : B →ₐ[O] O) (P : Fin q → Polynomial B) (act : PU R q n →ₐ[R] Module.End R V) (f : PU R q n) (α : Fin q → Fin n → O) (lam : M →+ O) (m₀ : M), TwoMaps (M := M) β.toRingHom P act f → (∀ j, (P j).map (x : B →+* O) = ∏ i, (Polynomial.X - Polynomial.C (α j i))) → (∀ (a : B) m, lam (a • m) = x a * lam m) → ∃ (lw : V →+ O) (v : V), (∀ τ w, lw (act τ w) = MvPolynomial.eval₂ ((x.comp β : R →ₐ[O] O) : R →+* O) (fun p => α p.1 p.2) τ * lw w) ∧ lw v = MvPolynomial.eval₂ ((x.comp β : R →ₐ[O] O) : R →+* O) (fun p => α p.1 p.2) f * lam m₀ := by
  intro O R B M V _ _ _ _ _ _ _ _ _ q n β x P act f α lam m₀ hT hP hlam
  obtain ⟨φ, ψ, h1, h2, h3, h4⟩ := hT
  letI : Algebra B O := (x : B →+* O).toAlgebra
  let ε : MSplitAlg P n →ₐ[B] O := MSplitAlg.lift P n (fun j i => α j i) (fun j => (hP j).symm)
  have hε : ∀ t : PU R q n, ε (Ideal.Quotient.mk (mSplitIdeal P n) (MvPolynomial.map β.toRingHom t)) =
      MvPolynomial.eval₂ ((x.comp β : R →ₐ[O] O) : R →+* O) (fun p => α p.1 p.2) t := by
    intro t
    show MvPolynomial.aeval (fun p : Fin q × Fin n => α p.1 p.2) (MvPolynomial.map β.toRingHom t) = _
    rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_map]
    rfl
  let lamL : M →ₗ[B] O :=
    { toFun := lam
      map_add' := lam.map_add
      map_smul' := fun a m => hlam a m }
  let Λ : MSplitAlg P n ⊗[B] M →ₗ[B] O :=
    TensorProduct.lift ((LinearMap.mul B O).compl₁₂ ε.toLinearMap lamL)
  have hΛt : ∀ a m, Λ (a ⊗ₜ m) = ε a * lam m := by
    intro a m
    show TensorProduct.lift _ (a ⊗ₜ m) = _
    rw [TensorProduct.lift.tmul]
    rfl
  have hΛs : ∀ (a : MSplitAlg P n) z, Λ (a • z) = ε a * Λ z := by
    intro a z
    induction z using TensorProduct.induction_on with
    | zero => rw [smul_zero, map_zero, mul_zero]
    | tmul a' m => rw [TensorProduct.smul_tmul', smul_eq_mul, hΛt, hΛt, map_mul, mul_assoc]
    | add z₁ z₂ h₁ h₂ => rw [smul_add, map_add (f := _), map_add (f := _), h₁, h₂, mul_add]
  refine ⟨Λ.toAddMonoidHom.comp ψ, φ (1 ⊗ₜ m₀), ?_, ?_⟩
  · intro τ w
    show Λ (ψ (act τ w)) = _ * Λ (ψ w)
    rw [h2, hΛs, hε]
  · show Λ (ψ (φ (1 ⊗ₜ m₀))) = _
    rw [h4, hΛs, hε, hΛt, map_one, one_mul]
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.SpectralEigenvalues.FElMap

section

@[expose] public section

open IsLocalRing Matrix Filter UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.Lev UpperTheory.V.AlgebraTools UpperTheory.V.Th
open scoped TensorProduct

private theorem fEl_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {q n : ℕ} (Nq : Fin q → ℕ) (u : Fin q → Fin n → R) :
    f (fEl Nq u) = fEl Nq fun j i => f (u j i) := by
  simp [fEl]

private theorem chi_rep {n : ℕ} {A G : Type} [CommRing A] [Group G] (ρ : G →* Matrix (Fin n) (Fin n) A) (g : G) :
    (GDet.ofRep ρ).chi (MonoidAlgebra.single g 1) = (ρ g).charpoly := by
  change (GDet.repAlg ρ (Polynomial A) _).det = _
  rw [map_sub, MonoidAlgebra.mapRingHom_single, Matrix.charpoly]
  congr 1
  ext i j : 2
  by_cases h : i = j <;> simp [GDet.repAlg, Matrix.charmatrix, h, Matrix.one_apply, Matrix.diagonal_apply]

private theorem g_dvd {O : Type} [CommRing O] {q n : ℕ} (Nq : Fin q → ℕ) (α : Fin q → Fin n → O) :
    (∏ j, ∏ i, ∏ k ∈ Finset.univ.erase i, (α j i - α j k)) ∣ fEl Nq α :=
  Finset.prod_dvd_prod_of_dvd _ _ fun _ _ => Finset.prod_dvd_prod_of_dvd _ _ fun _ _ =>
    Finset.prod_dvd_prod_of_dvd _ _ fun _ _ => dvd_mul_right _ _

private theorem e_dvd {O : Type} [CommRing O] {q n : ℕ} (α : Fin q → Fin n → O) (j : Fin q) (i : Fin n) :
    (∏ k ∈ Finset.univ.erase i, (α j i - α j k)) ∣ ∏ j, ∏ i, ∏ k ∈ Finset.univ.erase i, (α j i - α j k) :=
  (Finset.dvd_prod_of_mem (fun i => ∏ k ∈ Finset.univ.erase i, (α j i - α j k)) (Finset.mem_univ i)).trans
    (Finset.dvd_prod_of_mem (fun j => ∏ i, ∏ k ∈ Finset.univ.erase i, (α j i - α j k)) (Finset.mem_univ j))

private theorem num_dvd {O : Type} [CommRing O] (a g F e z c : O) (E : ℕ) (h1 : g ∣ F) (h2 : e ∣ F)
    (h : a ^ 2 * z * F ^ (3 * E + 6) ∣ c) : (a * g * F * F ^ E) ^ 2 * (F * z) * e ^ (E + 1) ∣ c := by
  refine Dvd.dvd.trans ?_ h
  obtain ⟨g', hg⟩ := h1
  obtain ⟨e', he⟩ := h2
  refine ⟨g' ^ 2 * e' ^ (E + 1), ?_⟩
  have : F ^ (3 * E + 6) = (g * g') ^ 2 * (F * F ^ E) ^ 2 * F * (e * e') ^ (E + 1) := by
    rw [← hg, ← he]; ring
  rw [this]; ring

theorem UpperTheory.V.Th.Sp.one :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 G : Glob l L) (h : G.Hom G0) (n : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (r : Resid G0.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (J : Ideal B) (D : ℕ) (b : TWBase u J Empty D) (q N : ℕ) (A : OpMod b h q N) (y : Pt G0.frame O n) (x : B →ₐ[O] O) (Nq : Fin q → ℕ) (ph ta : Fin q → G.G₀) (E : ℕ) (α : Fin q → Fin n → O) (t₀ : B) (lam : b.M →+ O) (m₀ : b.M) (m : ℕ) (c : O), 1 ≤ n → GenBy O (pairVals u) → u.Maps x.toRingHom (GDet.ofRep (mat y.ρ)) y.ψ → (∀ a : B, x a = 0 → ∀ w : b.M, (t₀ * a) • w ∈ wtSub b x) → (∀ (a : B) w, lam (a • w) = x a * lam w) → (∀ j, h.p₀ (ta j) = 1) → (∀ j, (mat y.ρ (h.p₀ (ph j))).charpoly = ∏ k, (Polynomial.X - Polynomial.C (α j k))) → OpRelX A Nq ph ta E → m ≤ N → x t₀ ^ 2 * lam m₀ * fEl Nq α ^ (3 * E + 6) ∣ c → ∀ a : Fin D ⊕ Fin q × Fin n, ∃ δ : A.R →ₗ[O] Om O m, IsDer (x.comp A.β) δ ∧ (∀ k, δ (algebraMap (abelian₂ O Empty D) A.R (MvPowerSeries.X (.inr k))) = if a = .inl k then algebraMap O _ c else 0) ∧ ∀ j i, δ (A.p.D.tr (twoPowerModulus E (ph j) (ta j) (fun k => algebraMap O A.R (α j k)) i 0)) = if a = .inr (j, i) then algebraMap O _ c else 0 := by
  intro l _ L G0 G h n O _ _ _ _ _ r B _ _ _ u J D b q N A y x Nq ph ta E α t₀ lam m₀ m c hn hgen hmap hEt hlam hta hα hA hN hc a
  have hs := Sp.betaSurj l L G0 G h n O r B u J D b q N A hgen
  have hβ := Sp.betaLam l L G0 G h n O r B u J D b q N A
  obtain ⟨t₁, rfl⟩ := hs t₀
  have hP : ∀ j, (u.D.chi (MonoidAlgebra.single (h.p₀ (ph j)) 1)).map (x : B →+* O) =
      ∏ i, (Polynomial.X - Polynomial.C (α j i)) := fun j => by
    have h1 := ((UpperTheory.V.CA.d_gmap u.D).2.2.1 x.toRingHom (MonoidAlgebra.single (h.p₀ (ph j)) 1)).1
    rw [MonoidAlgebra.mapRingHom_single, map_one, hmap.1, chi_rep, hα j] at h1
    exact h1.symm
  obtain ⟨lw, v₀, hlw, hv₀⟩ := Sp.lamW O A.R B b.M A.Mw q n A.β x _ A.actw _ α lam m₀ hA.two hP hlam
  obtain ⟨htr, hker⟩ := Sp.trans A.R A.M1 A.Mw q n A.act1 A.actw A.tr A.tr_surj A.tr_ker A.tr_u
  obtain ⟨v, rfl⟩ := A.tr_surj v₀
  let xU : PU A.R q n →+* O := MvPolynomial.eval₂Hom ((x.comp A.β : A.R →ₐ[O] O) : A.R →+* O) fun p => α p.1 p.2
  let π : PUY A.R q n →ₐ[A.R] PU A.R q n := MvPolynomial.aeval (Sum.elim MvPolynomial.X 0)
  let xT : PUY A.R q n →ₐ[O] O :=
    { xU.comp (π : PUY A.R q n →+* PU A.R q n) with
      commutes' := fun o => by
        change xU (π (MvPolynomial.C (algebraMap O A.R o))) = o
        simp [xU, π] }
  have hxT : ∀ τ, xT τ = xU (π τ) := fun _ => rfl
  have hC : ∀ s, xT (MvPolynomial.C s) = x (A.β s) := fun s => by simp [hxT, xU, π]
  have hU : ∀ j k, xT (uV A.R j k) = α j k := fun j k => by simp [hxT, xU, π]
  have hY : ∀ j k, xT (yV A.R j k) = 0 := fun j k => by simp [hxT, xU, π]
  let I : Ideal A.R := (RingHom.ker (x.comp b.lam)).map (algebraMap (abelian₂ O Empty D) A.R)
  have hI : ∀ w, w ∈ wtSub b x → w ∈ (I.map A.β • ⊤ : Submodule B b.M) := fun w hw => by
    refine Submodule.smul_induction_on hw (fun s hs w _ => ?_) fun _ _ => add_mem
    rw [b.smul_lam, ← hβ]
    exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ hs)) trivial
  have hkill := Sp.kill O A.R B b.M A.Mw q n A.β x _ A.actw _ α I t₁ hs hA.two hP fun a ha w => hI _ (hEt a ha w)
  let t : PUY A.R q n := MvPolynomial.C t₁ * (∏ j, ∏ i, ∏ k ∈ Finset.univ.erase i,
    (uV A.R j i - MvPolynomial.C (algebraMap O A.R (α j k)))) * fEl Nq (uV A.R) * fEl Nq (uV A.R) ^ E
  have hF : xT (fEl Nq (uV A.R)) = fEl Nq α := by
    have := fEl_map (xT : PUY A.R q n →+* O) Nq (uV A.R)
    simpa [hU] using this
  have hxt : xT t = x (A.β t₁) * (∏ j, ∏ i, ∏ k ∈ Finset.univ.erase i, (α j i - α j k)) * fEl Nq α * fEl Nq α ^ E := by
    simp only [t, map_mul, map_pow, map_prod, map_sub, hC, hU, hF, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply]
  have hv : lw (A.tr v) = fEl Nq α * lam m₀ := by
    rw [hv₀]
    congr 1
    have := fEl_map xU Nq fun j i => MvPolynomial.X (j, i)
    simpa [xU] using this
  obtain ⟨del, hd, h1, h2, h3⟩ := Sp.derOp l L G0 G h n O r B u J D b q N A xT (lw.comp A.tr.toAddMonoidHom) t v I m hN hY
    (fun τ w => by
      change lw (A.tr (A.act1 τ w)) = xT τ * lw (A.tr w)
      rw [htr, hlw]; rfl)
    (Ideal.span_le.2 (by
      rintro _ ⟨s, hs, rfl⟩
      exact Ideal.subset_span ⟨s, rfl, by rw [hC, hβ]; exact hs⟩))
    (fun s hs w => hker I _ (by
      have hπ : π (fEl Nq (uV A.R)) = fEl Nq fun j i => MvPolynomial.X (j, i) := by
        have := fEl_map (π : PUY A.R q n →+* PU A.R q n) Nq (uV A.R)
        simpa [π] using this
      have e : π (t * s) = MvPolynomial.C t₁ * (∏ j, ∏ i, ∏ k ∈ Finset.univ.erase i,
          (MvPolynomial.X (j, i) - MvPolynomial.C (algebraMap O A.R (α j k)))) * (fEl Nq fun j i => MvPolynomial.X (j, i)) *
          π (fEl Nq (uV A.R) ^ E * s) := by
        simp only [t, map_mul, map_prod, map_sub, hπ, mul_assoc]
        simp [π]
      rw [htr]
      change A.actw (π (t * s)) _ ∈ _
      rw [e]
      refine hkill _ ?_ _
      change xT _ = 0
      rw [map_mul, hs, mul_zero])) a
  have hv' : (lw.comp A.tr.toAddMonoidHom) v = fEl Nq α * lam m₀ := hv
  rw [hv'] at h1 h2
  have hq : ∀ j i, del (MvPolynomial.C (A.p.D.tr (twoPowerModulus E (ph j) (ta j) (fun k => algebraMap O A.R (α j k)) i 0))) =
      (∏ k ∈ Finset.univ.erase i, (α j i - α j k)) ^ (E + 1) • del (yV A.R j i) := fun j i => by
    obtain ⟨k1, k2⟩ := Sp.q2op l L G0 G h n O r B u J D b q N A y x (ph j) (ta j) (α j) E j i xT _ del hn hmap (hta j) (hα j)
      hC (hU j) (hY j i) hd
    have := h3 _ k1 (by
      simp only [t]
      rw [mul_assoc, map_mul, hA.rel2, mul_zero])
    rw [this] at k2
    exact sub_eq_zero.1 k2.symm
  let δ₀ : A.R →ₗ[O] Om O m := del ∘ₗ (IsScalarTower.toAlgHom O A.R (PUY A.R q n)).toLinearMap
  have hδ : ∀ s, δ₀ s = del (MvPolynomial.C s) := fun _ => rfl
  have hder : ∀ e : O, IsDer (x.comp A.β) (e • δ₀) := fun e s s' => by
    simp only [LinearMap.smul_apply, hδ, map_mul, hd _ _, hC, AlgHom.comp_apply, smul_add, smul_comm e]
  have hnum := fun j i => num_dvd _ _ _ _ _ c E (g_dvd Nq α) ((e_dvd α j i).trans (g_dvd Nq α)) hc
  have hn0 := num_dvd _ _ _ 1 _ c E (g_dvd Nq α) (one_dvd _) hc
  rw [← hxt] at hnum hn0
  rcases a with k | ⟨j, i⟩
  · obtain ⟨e, he⟩ := hn0
    refine ⟨e • δ₀, hder e, fun k' => ?_, fun j i => ?_⟩
    · rw [LinearMap.smul_apply, hδ, h1]
      split_ifs
      · rw [he, Algebra.smul_def, ← map_mul]; congr 1; ring
      · simp
    · rw [LinearMap.smul_apply, hδ, hq, h2]; simp
  · obtain ⟨e, he⟩ := hnum j i
    refine ⟨e • δ₀, hder e, fun k' => ?_, fun j' i' => ?_⟩
    · rw [LinearMap.smul_apply, hδ, h1]; simp
    · rw [LinearMap.smul_apply, hδ, hq, h2]
      split_ifs with hh
      · obtain ⟨rfl, rfl⟩ : j = j' ∧ i = i' := by simpa using hh
        rw [he, Algebra.smul_def, Algebra.smul_def, ← map_mul, ← map_mul]; congr 1; ring
      · simp
end
end
