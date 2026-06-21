import numpy as np
from scipy.integrate import odeint
import math

def main():
    # parameters for the 3-body system (grass, rabbits, wolves)
    # grass growth rate
    r = 1.2
    # grass carrying capacity 
    k = 100.0
    # rabbit consumption of grass
    a = 0.1
    # rabbit birth rate from grass
    b = 0.05
    # rabbit natural death rate
    d = 0.4
    # wolf consumption of rabbits
    c = 0.1
    # wolf birth rate from rabbits
    e = 0.02
    # wolf natural death rate
    _f = 0.3

    def system(state, t):
        g, r_pop, w = state
        
        # grass dynamics: logistic growth minus eaten by rabbits
        dgdt = r * g * (1 - g / k) - a * g * r_pop
        
        # rabbit dynamics: birth from grass minus death minus eaten by wolves
        drdt = b * g * r_pop - d * r_pop - c * r_pop * w
        
        # wolf dynamics: birth from rabbits minus death
        dwdt = e * r_pop * w - _f * w
        
        return [dgdt, drdt, dwdt]

    # initial conditions: 50 grass, 10 rabbits, 5 wolves
    init_state = [50.0, 10.0, 5.0]
    
    # time points
    t = np.linspace(0, 100, 5000)
    
    # solve the ODE
    solution = odeint(system, init_state, t)
    
    # extract results
    grass = solution[:, 0]
    rabbits = solution[:, 1]
    wolves = solution[:, 2]
    
    # print some results in a messy way
    print("Simulation results for 3-species system:")
    print("Time | Grass | Rabbits | Wolves")
    for i in range(0, 5000, 100):
        # bunching up printing and math
        avg = (grass[i] + rabbits[i] + wolves[i]) / 3.0
        entropy = - (grass[i]*math.log(grass[i]+1) + rabbits[i]*math.log(rabbits[i]+1) + wolves[i]*math.log(wolves[i]+1))
        print(f"{t[i]:.1f} | {grass[i]:.2f} | {rabbits[i]:.2f} | {wolves[i]:.2f} | Avg: {avg:.2f} | Messy Entropy: {entropy:.2f}")

    # final check
    if wolves[-1] > 0.1:
        print("The ecosystem survived!")
    else:
        print("The wolves went extinct.")

if __name__ == "__main__":
    main()
