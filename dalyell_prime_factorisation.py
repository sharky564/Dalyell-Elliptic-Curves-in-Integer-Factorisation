import time
import math
import random
import numpy as np
from bisect import bisect

# extended euclidean algorithm
def bin_euclid(num_1, num_2): 

    flag_1 = (num_1 < num_2)
    if flag_1:
        temp = num_1
        num_1 = num_2
        num_2 = temp

    if num_2 == 0:
        if flag_1:
            return (0, 1, num_1)
        else:
            return (1, 0, num_1)

    else:
        quotient, rem = divmod(num_1, num_2)
        num_1 = num_2
        num_2 = rem
        if num_2 == 0:
            if flag_1:
                return (1, 0, num_1)
            else:
                return (0, 1, num_1)

        else:
            power_of_two = 0
            while not (num_1 & 1) and not (num_2 & 1):
                power_of_two += 1
                num_1 >>= 1
                num_2 >>= 1

            flag_2 = not (num_2 & 1)
            if flag_2:
                temp = num_1
                num_1 = num_2
                num_2 = temp

            coeff_1 = 1
            gcd_num = num_1
            par_2_coeff_1 = num_2
            par_2_coeff_3 = num_2

            if num_1 & 1:
                par_1_coeff_1 = 0
                par_1_coeff_3 = -num_2

            else:
                par_1_coeff_1 = (num_2 + 1) >> 1
                par_1_coeff_3 = num_1 >> 1
                while not (par_1_coeff_3 & 1):
                    par_1_coeff_3 >>= 1
                    if (par_1_coeff_1 & 1):
                        par_1_coeff_1 = (par_1_coeff_1 + num_2) >> 1
                    else:
                        par_1_coeff_1 >>= 1

            if par_1_coeff_3 > 0:
                coeff_1 = par_1_coeff_1
                gcd_num = par_1_coeff_3

            else:
                par_2_coeff_1 = num_2 - par_1_coeff_1
                par_2_coeff_3 = -par_1_coeff_3

            par_1_coeff_1 = coeff_1 - par_2_coeff_1
            par_1_coeff_3 = gcd_num - par_2_coeff_3

            if par_1_coeff_1 < 0:
                par_1_coeff_1 += num_2

            while par_1_coeff_3 != 0:
                while not (par_1_coeff_3 & 1):
                    par_1_coeff_3 >>= 1
                    if (par_1_coeff_1 & 1): 
                        par_1_coeff_1 = (par_1_coeff_1 + num_2) >> 1
                    else:
                        par_1_coeff_1 >>= 1

                if par_1_coeff_3 > 0:
                    coeff_1 = par_1_coeff_1
                    gcd_num = par_1_coeff_3

                else:
                    par_2_coeff_1 = num_2 - par_1_coeff_1
                    par_2_coeff_3 = -par_1_coeff_3

                par_1_coeff_1 = coeff_1 - par_2_coeff_1
                par_1_coeff_3 = gcd_num - par_2_coeff_3

                if par_1_coeff_1 < 0:
                    par_1_coeff_1 += num_2

            coeff_2 = (gcd_num - num_1 * coeff_1) // num_2
            gcd_num <<= power_of_two
            if flag_2:
                temp = coeff_1
                coeff_1 = coeff_2
                coeff_2 = temp

            coeff_1 -= coeff_2 * quotient

            if flag_1:
                return (coeff_1, coeff_2, gcd_num)
            else:
                return (coeff_2, coeff_1, gcd_num)
    
# modular inverse
def inverse(base, modulus): 
    inv, fac, d = bin_euclid(base, modulus)
    invertible = (d == 1)
    if invertible:
        return invertible, inv % modulus
    else:
        return invertible, [base, modulus, d]


# bit-slicing
def inclusive_digit(number, index_1, index_2): 
    return (((1 << (index_2 - index_1 + 1)) - 1) & (number >> index_1))

# converting numbers to binary for grouping
def flexible(number, base): 
    odd=[]
    indices = []

    indices.append(int(math.log2(number & (~(number - 1)))))
    index = 0
    curr_idx = indices[0]

    odd.append(inclusive_digit(number, curr_idx, curr_idx + base - 1))

    new_number = (number >> (curr_idx + base))
    while new_number != 0:
        index += 1
        indices.append(int(math.log2(new_number & (~(new_number - 1)))) + base)

        curr_idx += indices[index]
        odd.append(inclusive_digit(number, curr_idx, curr_idx + base - 1))

        new_number = (number >> (curr_idx + base))
    else:
        return odd, indices, index

# grouping constant for sliding window
vals = [(k + 1) * (k + 2) * pow(2, k-1) + 1 for k in range(1, 55)]
def group_cons_func(num, breakpoints=vals):
    if num <= (1 << 64):
        return bisect(breakpoints, num) + 1
    else:
        return 55

# efficient exponentiation
def power(base, index, modulus=0): 
    if index == 0:
        return 1
    else:
        if index < 0:
            abs_index = -index
            new_base = 1/base
            if modulus:
                invertible, new_base = inverse(base, modulus)
                if not invertible:
                    raise ValueError(f"{base} is not invertible in mod {modulus}")
                
        else:
            abs_index = index
            new_base = base
            if modulus:
                new_base %= modulus
        
        logval = math.log2(abs_index)
        group_cons = group_cons_func(logval)

        odd, indices, len_val = flexible(abs_index, group_cons)
        curr_idx = len_val

        squared = new_base * new_base
        if modulus:
            squared %= modulus
        odd_powers = [new_base]
        for _ in range(3, (1 << group_cons), 2):
            next_val = odd_powers[-1] * squared
            if modulus:
                next_val %= modulus
            odd_powers.append(next_val)

        if curr_idx == len_val:
            prod = odd_powers[(odd[curr_idx]-1) >> 1]
        else:
            prod *= odd_powers[(odd[curr_idx]-1) >> 1]
            if modulus:
                prod %= modulus
        
        for _ in range(indices[curr_idx]):
            prod *= prod
            if modulus:
                prod %= modulus
        
        while curr_idx != 0:
            curr_idx -= 1
            if curr_idx == len_val:
                prod = odd_powers[(odd[curr_idx]-1) >> 1]
            else:
                prod *= odd_powers[(odd[curr_idx]-1) >> 1]
                if modulus:
                    prod %= modulus
            
            for _ in range(indices[curr_idx]):
                prod *= prod
                if modulus:
                    prod %= modulus
        else:
            return prod

# euler totient function
def euler_totient(n): 
    value = n
    prime_dict = factorint(n)
    for p in prime_dict:
        value //= p
        value *= p-1
    return value

# order of an element in multiplicative group
def order(g, group): 
    h = euler_totient(group)
    prime_dict = factorint(h)
    prime_factors = [(i, prime_dict[i]) for i in prime_dict]
    k = len(prime_factors)
    e = h
    i = 0
    while i < k:
        p_i = prime_factors[i][0]
        v_i = prime_factors[i][1]
        e //= power(p_i, v_i)
        g_1 = power(g, e, group)
        while g_1 != 1:
            g_1 = power(g_1, p_i, group)
            e *= p_i
        i += 1
    else:
        return e

# finds primitive root in mod p
def primitive_root(p): 
    prime_dict = factorint(p-1)
    primes = [i for i in prime_dict]
    k = len(primes)
    i = 0
    a = 2
    while i < k:
        p_i = primes[i]
        e = pow(a, (p - 1) // p_i, p)
        if e != 1:
            i += 1
        else:
            a += 1
            i = 0
    else:
        return a
		
# checks if num is a QR in the mod
def QR_kronecker(num, mod): 
    if mod == 0:
        if abs(num) != 1:
            return 0
        else:
            return 1
    else:
        if not (num & 1) and not (mod & 1):
            return 0
        else:
            powers_of_neg_1 = [0, 1, 0, -1, 0, -1, 0, 1]
            powers_of_two = 0
            while not (mod & 1):
                powers_of_two += 1
                mod >>= 1
            if not (powers_of_two & 1):
                output = 1
            else:
                output = powers_of_neg_1[num & 7]
            if mod < 0:
                mod = -mod
                if num < 0:
                    output = -output
            while num != 0:
                powers_of_two = 0
                while not (num & 1):
                    powers_of_two += 1
                    num >>= 1
                if (powers_of_two & 1):
                    output *= powers_of_neg_1[mod & 7]
                if (num & mod & 2):
                    output = -output
                rem = abs(num)
                num = mod % rem
                mod = rem
                if num > (rem >> 1):
                    num -= rem
            else:
                if mod > 1:
                    return 0
                else:
                    return output

# checks if num is QR in the mod
def bin_kronecker(num, mod): 
    if mod == 0:
        if abs(num) != 1:
            return 0
        else:
            return 1
    else:
        if not (num & 1) and not (mod & 1):
            return 0
        else:
            powers_of_neg_1 = [0, 1, 0, -1, 0, -1, 0, 1]
            powers_of_two = 0
            while not (mod & 1):
                powers_of_two += 1
                mod >>= 1
            if not (powers_of_two & 1):
                output = 1
            else:
                output = powers_of_neg_1[num & 7]
            if mod < 0:
                mod = -mod
                if num < 0:
                    output = -output
            while num != 0:
                powers_of_two = 0
                while not (num & 1):
                    powers_of_two += 1
                    num >>= 1
                if (powers_of_two & 1):
                    output = powers_of_neg_1[mod & 7]
                rem = mod - num
                if rem > 0:
                    if (num & mod & 2):
                        output = -output
                    mod = num
                    num = rem
                else:
                    num = -rem
            else:
                if mod > 1:
                    return 0
                else:
                    return output

#sqrt in mod prime
def mod_sqrt(num, prime): 
    if num == 0:
        return 0
    else:
        e = 0
        q = prime - 1
        while not (q & 1):
            e += 1
            q >>= 1
        
        n = random.randint(1, prime - 1)
        while QR_kronecker(n, prime) != -1:
            n = random.randint(1, prime - 1)
        z = pow(n, q, prime)

        y = z
        r = e
        x = pow(num, (q - 1) >> 1, prime)
        b = (num * x * x) % prime
        x = (num * x) % prime

        flag = 0
        while b % prime != 1 and not flag:
            m = 1
            while pow(b, 1 << m, prime) != 1:
                m += 1
            if m == r:
                flag = 1
            else:
                t = pow(y, 1 << (r - m - 1), prime)
                y = (t * t) % prime
                r = m % prime
                x = (x * t) % prime
                b = (b * y) % prime
        else:
            if flag:
                raise ValueError(f"square root of {num} doesn't exist mod {prime}")
            else:
                return x

# x^2 + dy^2 = p
def prime_pell(d, p): 
    if d >= p or d <= 0:
        raise ValueError
    else:
        k = QR_kronecker(-d, p)
        if k == -1:
            raise ValueError
        else:
            x_0 = mod_sqrt(-d, p)
            if x_0 < (p >> 1):
                x_0 = p - x_0
            a = p
            b = x_0
            l = int(np.sqrt(p))
            while b > l:
                r = a % b
                a = b
                b = r
            if (p - b * b) % d != 0 or (c := (p - b * b) // d) != (p - b * b) / d:
                raise ValueError(f"x^2 + {d}y^2={p} has no solutions")
            else:
                return (b, np.sqrt(c))

# x^2 + |d|y^2 = 4p
def mod_prime_pell(d, p): 
    if p == 2:
        if int(np.sqrt(d + 8)) == np.sqrt(d + 8):
            return (np.sqrt(d + 8), 1)
        else:
            raise ValueError(f"x^2 + |{d}|y^2=4{p} has no solutions")
    else:
        k = QR_kronecker(d, p)
        if k == -1:
            raise ValueError
        else:
            x_0 = mod_sqrt(d, p)
            if not ((x_0 & 1) ^ (d & 1)):
                x_0 = p - x_0
            a = p << 1
            b = x_0
            l = int(2 * np.sqrt(p))
            while b > l:
                r = a % b
                a = b
                b = r
            else:
                if ((p << 2) - b * b) % d != 0 or (c := ((p << 2) - b * b) // d) != (p - b * b) / d:
                    raise ValueError(f"x^2 + |{d}|y^2=4{p} has no solutions")
                else:
                    return (b, np.sqrt(c))


############################################################

# Generate small primes up to a million for small stuff
very_small_file = open('very_small_primes.txt', 'r')
lines = very_small_file.readlines()
very_small_primes = list(map(int, [line.strip().split(', ') for line in lines][0]))

# Generate primes up to a million for "small cases"
small_file = open('small_primes.txt', 'r')
lines = small_file.readlines()
small_primes = list(map(int, [line.strip().split(', ') for line in lines][0]))

# Generate prime differences up to a million
prime_diff_file = open('prime_diffs.txt', 'r')
lines = prime_diff_file.readlines()
prime_diffs = list(map(int, [line.strip().split(', ') for line in lines][0]))

# Generate primes up to a 2 million for big stuff
big_file = open('primes_under_2mil.txt', 'r')
lines = big_file.readlines()
big_primes = list(map(int, [line.strip().split(', ') for line in lines][0]))

# Factorising numbers with small primes
def small_factors(n, factors=[]):
    if n == 1:
        factors.append(1)
        return factors
    else:
        i = 0
        prime_found = False
        while i < len(small_primes) and not prime_found:
            prime = small_primes[i]
            if n % prime == 0:
                k = 0
                while n % prime == 0:
                    n //= prime
                    k += 1
                factors.append((prime, k))
                prime_found = True
                break
            else:
                i += 1
        if prime_found:
            return small_factors(n, factors)
        else:
            factors.append(n)
            return factors

# For Miller-Rabin Primality Testing
def try_composite(a, d, n, s):
    if pow(a, d, n) == 1:
        return False
    for i in range(s):
        if pow(a, (1 << i) * d, n) == n-1:
            return False
    return True

# Miller-Rabin Primality Testing, deterministic for up to 2^64
def miller_rabin(n, precision_for_huge_n=16):
    if any((n % p) == 0 for p in small_primes) or n in (0, 1):
        return False
    d, s = n - 1, 0
    while not (d & 1):
        d, s = d >> 1, s + 1
    if n < (1 << 64): 
        if n == 299210837:
            return True
        else:
            return not any(try_composite(a, d, n, s) for a in (2, 325, 9375, 28178, 450775, 9780504, 1795265022))
    else:
        return not any(try_composite(a, d, n, s) for a in small_primes[:precision_for_huge_n])

# Pollard p-1 method
def pollard(N, B=1000000):
    if B != 1000000:
        prime_list = list(sieve.primerange(1, B))
    else:
        prime_list = small_primes
    k = len(prime_list)

    x = 2 # set x = 3 if last while loop fails
    y = x
    c = 0
    i = 0
    j = i
    
    i += 1
    backtrack_flag = False
    while not backtrack_flag:
        if c < 20:
            if i > k:
                g = math.gcd(x-1, N)
                if g == 1:
                    raise ValueError
                else:
                    i = j
                    x = y
                    backtrack_flag = True
            else:
                q = prime_list[i - 1]
                q_1 = q
                l = B // q
                while q_1 <= l:
                    q_1 *= q
                x = pow(x, q_1, N)
                c += 1
        else:
            g = bin_euclid(x-1, N)[2]
            if g == 1:
                c = 0
                j = i
                y = x
            else:
                i = j
                x = y
                backtrack_flag = True
    finished_flag = False
    while not finished_flag:
        i += 1
        q = prime_list[i - 1]
        q_1 = q
        x = pow(x, q, N)
        g = math.gcd(x-1, N)
        backtrack2_flag = False
        while not backtrack2_flag:
            if g == 1:
                q_1 *= q
                if q_1 <= B:
                    x = pow(x, q, N)
                    g = math.gcd(x-1, N)
                else:
                    backtrack2_flag = True
            else:
                if g < N:
                    backtrack2_flag = True
                    finished_flag = True
                    return g
                else:
                    raise ValueError

# medium_file = open('primes_under_2mil.txt', 'r')
# lines = small_file.readlines()
# b1_primes = [line.strip().split(,) for line in lines][0]
# bigfile = open('primes_under_2^32.txt', 'r')
# lines = small_file.readlines()
# b2_primes = [line.strip().split(,) for line in lines][0]
# b2_diffs = [b2_primes[i] - b2_primes[i-1] for i in range(1, len(b2_primes))]


def pollard_factor(n, factors=[]):
    if factors == []:
        factors = small_factors(n)
    if factors[-1] == 1:
        return factors
    else:
        try:
            num = factors.pop()
            p = pollard(num)
        except ValueError:
            factors.append(num)
            return factors
        k = 0
        while num % p == 0:
            num //= p
            k += 1
        factors.append((p, k))
        factors.append(num)
        return pollard_factor(num, factors)


# y^2 t = x^3 + a x t + t^3
# ECM Addition using projective points, without any division
def ECM_sum(point_1, point_2, a, mod):
    x1, y1, t1 = point_1
    x2, y2, t2 = point_2
    if point_1 == point_2:
        if y1 == 0:
            return False, (x1, y1, 0)
        else:
            T = (3 * x1**2 + a * t1**2) % mod
            U = (y1 * t1 << 1) % mod
            V = (U * x1 * y1 << 1) % mod
            W = (T**2 - 2 * V) % mod
            x3 = (U * W) % mod
            y3 = (T * (V - W) - 2 * (U * y1)**2) % mod
            t3 = (U**3) % mod
            invertible = (t3 != 0)
            if invertible:
                return invertible, (x3, y3, t3)
            else:
                return invertible, (point_1, point_2, a, mod)
    else:
        if (x1 * t2 - x2 * t1) % mod == 0:
            return (False, (x1, y1, 0))
        else:
            T0 = (y1 * t2) % mod
            T1 = (y2 * t1) % mod
            T = (T0 - T1) % mod
            U0 = (x1 * t2) % mod
            U1 = (x2 * t1) % mod
            U = (U0 - U1) % mod
            U2 = (U**2) % mod
            U3 = (U * U2) % mod
            V = (t1 * t2) % mod
            W = (T**2 * V - U2 * (U0 + U1)) % mod
            x3 = (U * W) % mod
            y3 = (T * (U0 * U2 - W) - T0 * U3) % mod
            t3 = (U3 * V) % mod
            invertible = (t3 != 0)
            if invertible:
                return invertible, (x3, y3, t3)
            else:
                return invertible, (point_1, point_2, a, mod)


# y^2 t = x^3 + a x t + t^3
def ECM_prod(point_1, n, a, mod):
    if n == 1:
        return point_1
    else:
        logval = math.log2(n)
        group_cons = group_cons_func(logval)
        
        odd, indices, len_val = flexible(n, group_cons)
        curr_idx = len_val

        invertible, temp_doubled = ECM_sum(point_1, point_1, a, mod)
        if not invertible:
            return invertible, (point_1, point_1, a, mod)
        else:
            doubled = temp_doubled
        odd_sums = [point_1]
        for _ in range(3, (1 << group_cons), 2):
            invertible, temp_next_val = ECM_sum(odd_sums[-1], doubled, a, mod)
            if not invertible:
                return invertible, (odd_sums[-1], doubled, a, mod)
            else:
                next_val = temp_next_val
            odd_sums.append(next_val)
        
        if curr_idx == len_val:
            prod = odd_sums[(odd[curr_idx]-1) >> 1]
        else:
            invertible, temp_prod = ECM_sum(prod, odd_sums[(odd[curr_idx]-1) >> 1], a, mod)
            if not invertible:
                return invertible, (prod, odd_sums[(odd[curr_idx]-1) >> 1], a, mod)
            else:
                prod = temp_prod
        
        for _ in range(indices[curr_idx]):
            invertible, temp_prod = ECM_sum(prod, prod, a, mod)
            if not invertible:
                return invertible, (prod, prod, a, mod)
            else:
                prod = temp_prod
        
        while curr_idx != 0:
            curr_idx -= 1
            if curr_idx == len_val:
                prod = odd_sums[(odd[curr_idx]-1) >> 1]
            else:
                invertible, temp_prod = ECM_sum(prod, odd_sums[(odd[curr_idx]-1) >> 1], a, mod)
                if not invertible:
                    return invertible, (prod, odd_sums[(odd[curr_idx]-1) >> 1], a, mod)
                else:
                    prod = temp_prod
            
            for _ in range(indices[curr_idx]):
                invertible, temp_prod = ECM_sum(prod, prod, a, mod)
                if not invertible:
                    return invertible, (prod, prod, a, mod)
                else:
                    prod = temp_prod
        
        else:
            return True, prod

def lenstra_ECM_S2(large_num, point, coeff):
    temp_point = point
    y_point = point
    g = 0
    P = 1
    i = 0
    j = 0
    c = 0
    point_diffs = []
    used_diffs = {}
    for k in range(0, len(prime_diffs)):
        if prime_diffs[k] in used_diffs:
            point_diffs.append(used_diffs[prime_diffs[k]])
        else:
            invertible, new = ECM_prod(point, prime_diffs[k], coeff, large_num)
            if not invertible:
                # print(f"Points {new[0], new[1]} not summable for a={new[2]} in mod {large_num}, checking for factor")
                point_1 = new[0]
                point_2 = new[1]
                if point_1 != point_2:
                    check_1, inverse_1 = inverse(point_1[2], large_num)
                    check_2, inverse_2 = inverse(point_2[2], large_num)
                    if check_1 & check_2:
                        t = (point_1[0] * point_2[2] - point_2[0] * point_1[2]) % large_num
                        if t != 0:
                            notFound = False
                            return math.gcd(t, large_num)
                        else:
                            return -1
                    else:
                        if not check_1:
                            return inverse_1[2]
                        else:
                            return inverse_2[2]
                else:
                    check_1, inverse_1 = inverse(point_1[2], large_num)
                    if check_1:
                        t = (2 * point_1[1] * inverse_1) % large_num
                        if t != 0:
                            notFound = False
                            print(t)
                            return math.gcd(t, large_num)
                        else:
                            return -1
                    else:
                        return inverse_1[2]
            else:
                used_diffs[prime_diffs[k]] = new
                point_diffs.append(new)
    invertible, point = ECM_prod(point, very_small_primes[-1], coeff, large_num)
    while i < len(prime_diffs):
        invertible, temp_point_check = ECM_sum(temp_point, point_diffs[i], coeff, large_num)
        if not invertible:
            # print(f"Points {temp_point_check[0], temp_point_check[1]} not summable for a={temp_point_check[2]} in mod {large_num}, checking for factor")
            point_1 = temp_point_check[0]
            point_2 = temp_point_check[1]
            if point_1 != point_2:
                check_1, inverse_1 = inverse(point_1[2], large_num)
                check_2, inverse_2 = inverse(point_2[2], large_num)
                if check_1 & check_2:
                    t = (point_1[0] * point_2[2] - point_2[0] * point_1[2]) % large_num
                    if t != 0:
                        notFound = False
                        return math.gcd(t, large_num)
                    else:
                        return -1
                else:
                    if not check_1:
                        return inverse_1[2]
                    else:
                        return inverse_2[2]
            else:
                check_1, inverse_1 = inverse(point_1[2], large_num)
                if check_1:
                    t = (2 * point_1[1] * inverse_1) % large_num
                    if t != 0:
                        notFound = False
                        print(t)
                        return math.gcd(t, large_num)
                    else:
                        return -1
                else:
                    return inverse_1[2]
        else:
            temp_point = temp_point_check
        P *= temp_point[2]
        c += 1
        i += 1
        if c >= 50:
            g = math.gcd(P, large_num)
            if g == 1:
                c = 0
                j = i
                y_point = temp_point
            else:
                i = j
                temp_point = y_point
                while True:
                    invertible, temp_point_check = ECM_sum(temp_point, point_diffs[i], coeff, large_num)
                    if not invertible:
                        # print(f"Points {temp_point_check[0], temp_point_check[1]} not summable for a={temp_point_check[2]} in mod {large_num}, checking for factor")
                        point_1 = temp_point_check[0]
                        point_2 = temp_point_check[1]
                        if point_1 != point_2:
                            check_1, inverse_1 = inverse(point_1[2], large_num)
                            check_2, inverse_2 = inverse(point_2[2], large_num)
                            if check_1 & check_2:
                                t = (point_1[0] * point_2[2] - point_2[0] * point_1[2]) % large_num
                                if t != 0:
                                    notFound = False
                                    return math.gcd(t, large_num)
                                else:
                                    return -1
                            else:
                                if not check_1:
                                    return inverse_1[2] 
                                else:
                                    return inverse_2[2]
                        else:
                            check_1, inverse_1 = inverse(point_1[2], large_num)
                            if check_1:
                                t = (2 * point_1[1] * inverse_1) % large_num
                                if t != 0:
                                    notFound = False
                                    print(t)
                                    return math.gcd(t, large_num)
                                else:
                                    return -1
                            else:
                                return inverse_1[2]
                    else:
                        temp_point = temp_point_check
                    i += 1
                    g = math.gcd(temp_point[2], large_num)
                    if g > 1:
                        if g == large_num:
                            return -1
                        else:
                            return g
    g = math.gcd(P, large_num)
    if g == 1 or g == large_num:
        return -1
    else:
        return g

# Lenstra's Elliptic Curves Method
def lenstra_ECM(large_num, B=12000, c=20, stage=False):
    primes = [i for i in small_primes if i < B]
    num_primes = len(primes)
    coeff = 0
    counter = 0
    notFound = True
    while notFound:
        point = (0, 1, 1)
        curr_prime_idx = 0
        if curr_prime_idx >= num_primes:
            print("Stage 2 Required!")
            stage_2 = lenstra_ECM_S2(large_num, point, coeff)
            if stage_2 == -1:
                coeff += 1
                counter = 0
                point = (0, 1, 1)
                curr_prime_idx = 0
            else:
                return f"2.4. Factor of {large_num}: {stage_2}"
        else:
            prime = primes[curr_prime_idx]
            prime_power = prime
            l = B // prime
            while prime_power <= l:
                prime_power *= prime
            invertible, point = ECM_prod(point, prime_power, coeff, large_num)
            while invertible:
                counter += 1
                curr_prime_idx += 1
                if curr_prime_idx >= num_primes:
                    if stage:
                        print("Stage 2")
                        stage_2 = lenstra_ECM_S2(large_num, point, coeff)
                        if stage_2 == -1 or stage_2 == -2:
                            coeff += 1
                            counter = 0
                            point = (0, 1, 1)
                            curr_prime_idx = 0
                        else:
                            return f"2.4. Factor of {large_num}: {stage_2}"
                    else:
                        coeff += 1
                        counter = 0
                        point = (0, 1, 1)
                        curr_prime_idx = 0
                else:
                    prime = primes[curr_prime_idx]
                    prime_power = prime
                    l = B // prime
                    while prime_power <= l:
                        prime_power *= prime
                    invertible, point = ECM_prod(point, prime_power, coeff, large_num)
                    if invertible and counter % c == 0:
                        d = math.gcd(point[2], large_num)
                        if d != 1:
                            return f"1.1. Factor of {large_num}: {d}"
            else:
                if not invertible:
                    # print(f"Points {point[0], point[1]} not summable for a={point[2]} in mod {large_num}, checking for factor")
                    point_1 = point[0]
                    point_2 = point[1]
                    if point_1 != point_2:
                        check_1, inverse_1 = inverse(point_1[2], large_num)
                        check_2, inverse_2 = inverse(point_2[2], large_num)
                        if check_1 & check_2:
                            t = (point_1[0] * point_2[2] - point_2[0] * point_1[2]) % large_num
                            if t != 0:
                                notFound = False
                                return f"1.2. Factor of {large_num}: {math.gcd(t, large_num)}"
                            else:
                                coeff += 1
                                counter = 0
                        else:
                            if not check_1:
                                return f"1.3. Factor of {large_num}: {inverse_1[2]}" 
                            else:
                                return f"1.4. Factor of {large_num}: {inverse_2[2]}"
                    else:
                        check_1, inverse_1 = inverse(point_1[2], large_num)
                        if check_1:
                            t = (2 * point_1[1] * inverse_1) % large_num
                            if t != 0:
                                notFound = False
                                print(t)
                                return f"1.5. Factor of {large_num}: {math.gcd(t, large_num)}" 
                            else:
                                coeff += 1
                                counter = 0
                        else:
                            return f"1.6. Factor of {large_num}: {inverse_1[2]}"



test_file = open("Numbers_to_factorise.txt", 'r')
lines = test_file.readlines()
test_cases = list(map(int, [line.strip() for line in lines]))
for number in test_cases:
    start_time = time.time()
    print(lenstra_ECM(number, B=200000, stage=False))
    print(f"------ Found in {time.time() - start_time} seconds ------\n")
