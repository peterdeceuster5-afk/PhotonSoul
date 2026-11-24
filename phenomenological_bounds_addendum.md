# Phenomenological Bounds on the Photon Soul Framework

## 1. Introduction
While the core calculus of the Photon Soul Continuity framework is fully verified via a zero-axiom Lean 4 mechanization (`PROOFPS.pdf`, Sections 1-4), the physical viability of the higher-dimensional bulk relies on phenomenological constraints. 

By integrating out the $(4+k)$-dimensional bulk, the effective field theory predicts a stochastic scalar coupling that degrades quantum phase coherence, leading to an interferometric fringe visibility loss:
$$ 1 - V = \mathcal{O}(1) \times \left(\frac{E}{\Lambda}\right)^{2k} $$
where $E$ is the photon energy, $\Lambda$ is the effective Kaluza-Klein mass scale of the bulk ($M_{KK} \sim \Lambda$), and $k$ represents the number of extra dimensions.

This addendum applies published observational data from both table-top interferometry and ultra-high-energy astrophysics to establish hard empirical lower bounds on the bulk scale $\Lambda$.

## 2. Table-Top Optical Interferometry (QUEST / Holometer)
Twin-interferometer experiments (such as the Fermilab Holometer and Cardiff's QUEST) are designed to detect stochastic, cross-correlated phase noise at high frequencies.

* **Experimental Limit:** These experiments achieve a high-frequency correlated phase variance limit of $\langle\delta\phi^2\rangle_{exp} \approx 10^{-40} \text{ rad}^2$.
* **Photon Energy:** Standard table-top setups utilize near-infrared lasers ($1064 \text{ nm}$), equating to a photon energy of $E \approx 1 \text{ eV} = 10^{-9} \text{ GeV}$.

By equating the theoretical phase variance $\langle\delta\phi^2\rangle \propto (E/\Lambda)^{4k}$ to the experimental limit, we can isolate $\Lambda$:
$$ \left(\frac{10^{-9} \text{ GeV}}{\Lambda}\right)^{4k} \approx 10^{-40} $$

* **For $k = 1$ (5D spacetime):** $\Lambda \gtrsim 10 \text{ GeV}$
* **For $k = 2$ (6D spacetime):** $\Lambda \gtrsim 100 \text{ keV}$

**Conclusion:** Due to the steep $(E/\Lambda)^{2k}$ energy suppression, optical photons are highly shielded from high-energy bulk fluctuations. Table-top interferometers can only rule out highly macroscopic or extremely low-energy extra dimensions.

## 3. Ultra-High-Energy Astrophysics (LHAASO)
To probe higher values of $\Lambda$ relevant to quantum gravity or string-theoretic compactifications, we must use the highest energy photons ever recorded. The Large High Altitude Air Shower Observatory (LHAASO) has definitively detected individual gamma rays arriving from the Cygnus star-forming region.

* **Experimental Observation:** Detection of a $1.42 \text{ PeV}$ gamma ray.
* **Photon Energy:** $E = 1.42 \times 10^6 \text{ GeV}$.

For this gamma ray to be detected as a directional point-source after traversing thousands of light-years, its quantum phase coherence cannot be completely destroyed by bulk stochastic fluctuations. Therefore, the visibility loss must be strictly less than total decoherence ($1 - V < 1$).

$$ \left(\frac{E}{\Lambda}\right)^{2k} \lesssim 1 \implies \Lambda \gtrsim E $$

**Conclusion:** The LHAASO dataset places a rigorous lower bound on the topological bulk scale:
$$ \Lambda \gtrsim 1.42 \times 10^6 \text{ GeV} \text{ (or } 1.42 \text{ PeV)} $$

## 4. Summary Implications
The available physical data successfully constrains but does not rule out the Photon Soul framework. The survival of PeV-scale cosmic gamma rays proves that if a higher-dimensional topological leakage exists, the extra dimensions must be tightly compactified with an effective energy scale strictly greater than $1.42 \text{ PeV}$. 