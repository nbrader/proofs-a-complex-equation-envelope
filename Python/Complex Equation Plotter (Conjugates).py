import pygame  # Version: 1.9.2a0
import pygame.freetype
from os import getcwd
from math import *

# VECTORS
def add_vec2(u, v):
    """Calculate the sum of two vectors, u and v.
    
    >>> add_vec2((3, 5), (3, 7))
    (6, 12)
    """
    return (u[0] + v[0], u[1] + v[1])

def scale_vec2(v, s):
    """Calculate vector v multiplied by scalar s.
    
    >>> scale_vec2((3, 5), 10)
    (30, 50)
    """
    return (s*v[0], s*v[1])

def mean_vec2(u, v):
    """Calculate the mean of two vectors, u and v.
    
    >>> mean_vec2((3, 5), (3, 7))
    (3, 6)
    """
    return scale_vec2(add_vec2(u,v), 0.5)

def rot90_vec2(v):
    """Calculate the result of rotating vector v by 90 degrees.
    
    >>> rot90_vec2((3, 5))
    (-5, 3)
    """
    return (-v[1], v[0])

def round_vec2(v):
    """Calculate the result of rounding vector vs.
    
    >>> round_vec2((3.1, 5.1))
    (3, 5)
    """
    return (round(v[0]), round(v[1]))

def neg_vec2(v):
    """Calculate additive inverse of vector v.
    
    >>> neg_vec2((3, 5))
    (-3, -5)
    """
    return scale_vec2(v, -1)

def diff_vec2(u, v):
    """Calculate difference of two vectors, u and v.
    
    >>> diff_vec2((3, 5), (3, 7))
    (0, -2)
    """
    return add_vec2(u, neg_vec2(v))

def square_vec2_norm(v):
    """Calculate the square of the Euclidean norm.
    
    Note that this operation is cheaper than vec2_norm.
    
    >>> square_vec2_norm((3, 5))
    34
    """
    return v[0]**2 + v[1]**2

def vec2_norm(a):
    """Calculate the Euclidean norm.
    
    >>> vec2_norm((3, 5))
    5.830951894845301
    """
    return square_vec2_norm(a)**0.5

def normalised_vec2(v):
    """Calculate the unit vector pointing in the same direction as v.
    
    >>> vec2_norm((3, 3))
    (sqrt(2)/2, sqrt(2)/2)
    """
    norm = vec2_norm(v)
    if norm == 0:
        return (0,0)
    else:
        return scale_vec2(v,1/norm)

def vec2_square_distance(a, b):
    """Calculate the square distance.
    
    Note that this operation is cheaper than vec2_distance.
    
    >>> vec2_square_distance((3, 5), (0, 0))
    34
    """
    return square_vec2_norm(diff_vec2(a, b))

def vec2_distance(a, b):
    """Calculate the distance.
    
    >>> vec2_distance((3, 5), (0, 0))
    5.830951894845301
    """
    return vec2_norm(diff_vec2(a, b))


# MAP SCREEN SPACE (to and from default coords)
SCREEN_SCALE = 100
def flip_y(p):
    return (p[0], -p[1])

def def_coords_to_screen(p):
    return round_vec2(add_vec2(flip_y(scale_vec2(p, SCREEN_SCALE)), SCREEN_CENTRE))

def screen_to_def_coords(p):
    return scale_vec2(flip_y(diff_vec2(p, SCREEN_CENTRE)), 1/SCREEN_SCALE)

def def_scale_to_screen_scale(p):
    return p*SCREEN_SCALE

def screen_scale_to_def_scale(p):
    return p/SCREEN_SCALE


# MAP COMPLEX NUMBERS (to and from default coords)
def def_coords_to_complex(v):
    return complex(v[0], v[1])

def complex_to_def_coords(z):
    return (z.real, z.imag)

def real_to_complex(s):
    return complex(s, 0)

TOL = 0.0001
def complex_to_real(z):
    if z.imag < TOL:
        return z.real
    else:
        raise Exception("NOT REAL ENOUGH!")


# COLOURS
BLACK      = (  0,   0,   0)
DARK_GREY  = ( 63,  63,  63)
GREY       = (127, 127, 127)
LIGHT_GREY = (191, 191, 191)
WHITE      = (255, 255, 255)

PINK    = (255, 127, 127)
RED     = (255,   0,   0)
GREEN   = (  0, 255,   0)
BLUE    = (127, 127, 255)
CYAN    = (  0, 255, 255)
MAGENTA = (255,   0, 255)
YELLOW  = (255, 255,   0)

DARK_RED     = (127,   0,   0)
DARK_GREEN   = (  0, 127,   0)
DARK_BLUE    = ( 63,  63, 191)
DARK_CYAN    = (  0, 127, 127)
DARK_MAGENTA = (127,   0, 127)
DARK_YELLOW  = (127, 127,   0)


# DRAWING
def draw_circle(surface, colour, pos, label = "", radius = 4, width = 0, text_offset = (-40,-10)):
    if radius >= width:
        pygame.draw.circle(surface, colour, def_coords_to_screen( pos ), radius, width)
        if label:
            draw_text(surface, colour, add_vec2(pos, scale_vec2(text_offset, 1/SCREEN_SCALE)), label)

def draw_line(surface, colour, pos1, pos2, label = "", width = 1):
    pygame.draw.line(surface, colour, def_coords_to_screen( pos1 ), def_coords_to_screen( pos2 ), width)
    if label:
        draw_text(surface, colour, mean_vec2(add_vec2(pos1, scale_vec2((12,5), 1/SCREEN_SCALE)), add_vec2(pos2, scale_vec2((12,5), 1/SCREEN_SCALE))), label)

def draw_arrow(surface, colour, tail, head, label = "", width = 1):
    arrow_points = get_arrow_points(def_coords_to_screen(tail), def_coords_to_screen(head), 3, 15, 10, 5, 5)
    for i in range(len(arrow_points)):
        prev_id = i - 1
        if (prev_id < 0):
            prev_id += len(arrow_points)

        this_point = arrow_points[i]
        prev_point = arrow_points[prev_id]
        
        draw_line(surface, colour, screen_to_def_coords(this_point), screen_to_def_coords(prev_point))
    if label:
        disp = scale_vec2(add_vec2(normalised_vec2(rot90_vec2(diff_vec2(tail,head))), (0,0.2)), 20/SCREEN_SCALE)
        draw_text(surface, colour, mean_vec2(add_vec2(tail, disp), add_vec2(head, disp)), label)

def get_arrow_points(tail, head, tail_width, head_width, head_length, gap_before_tail, gap_after_head):
    v = diff_vec2(head, tail)
    u = rot90_vec2(v)
    total_dist = vec2_norm(v)
    total_gap_target = gap_before_tail + gap_after_head;
    
    gap_after_head_adjusted = 0
    gap_before_tail_adjusted = 0
    head_length_actual = 0
    if (total_dist > 2 * head_length + total_gap_target):
        # use head_length and gaps
        gap_after_head_adjusted = gap_after_head
        gap_before_tail_adjusted = gap_before_tail
        head_length_actual = head_length
    elif (total_dist > 2 * head_length):
        # use head_length but not gaps
        totalGap_actual = total_dist - 2 * head_length
        gap_after_head_adjusted = totalGap_actual * (gap_after_head/total_gap_target)
        gap_before_tail_adjusted = totalGap_actual * (gap_before_tail / total_gap_target)
        head_length_actual = head_length
    else:
        # ignore head_length and gaps and just squash an arrow with half it's length as tail
        gap_after_head_adjusted = 0
        gap_before_tail_adjusted = 0
        head_length_actual = total_dist/2

    return [
        add_vec2(add_vec2(tail, scale_vec2(normalised_vec2(v),gap_before_tail_adjusted)), scale_vec2(normalised_vec2(u),(tail_width/2))),
        add_vec2(diff_vec2(head, scale_vec2(normalised_vec2(v),(gap_after_head_adjusted + head_length_actual))), scale_vec2(normalised_vec2(u),(tail_width/2))),
        add_vec2(diff_vec2(head, scale_vec2(normalised_vec2(v),(gap_after_head_adjusted + head_length_actual))), scale_vec2(normalised_vec2(u),(head_width/2))),
        diff_vec2(head, scale_vec2(normalised_vec2(v),gap_after_head_adjusted)),
        diff_vec2(diff_vec2(head, scale_vec2(normalised_vec2(v),(gap_after_head_adjusted + head_length_actual))), scale_vec2(normalised_vec2(u),(head_width/2))),
        diff_vec2(diff_vec2(head, scale_vec2(normalised_vec2(v),(gap_after_head_adjusted + head_length_actual))), scale_vec2(normalised_vec2(u),(tail_width/2))),
        diff_vec2(add_vec2(tail, scale_vec2(normalised_vec2(v),gap_before_tail_adjusted)), scale_vec2(normalised_vec2(u),(tail_width/2)))
    ]


# FONT
pygame.init()
FONT = pygame.freetype.Font(getcwd() + "\\Fonts\\LiberationSans-Regular.ttf", 20)

def draw_text(surface, colour, pos, text_string):
    screen_pos = def_coords_to_screen(pos)
    if screen_pos[0] > 0 and screen_pos[1] > 0:
        FONT.render_to(surface, screen_pos, text_string, colour)


# MAIN ROUTINE
SCREEN_WIDTH  = 1200
SCREEN_HEIGHT = 1200
SCREEN_CENTRE = (SCREEN_WIDTH//2, SCREEN_HEIGHT//2)
ORIGIN = (0,0)


NO_OF_ENVELOPE_POINTS = 100

main_surf = pygame.display.set_mode((SCREEN_WIDTH, SCREEN_HEIGHT))

p_left_mouse   = (-0.3,  0.5)
p_middle_mouse = ( 0.0, -0.5)
p_right_mouse  = ( 1.5,  0.5)

left_mouse_held = False
middle_mouse_held = False
right_mouse_held = False

show_one_e_at_a_time = False
show_more = False
show_envelope_attempt = False

main_loop = True
while main_loop:
    for event in pygame.event.get():
        if event.type == pygame.QUIT:
            main_loop = False
            break
        elif event.type == pygame.KEYDOWN:
            if event.key == pygame.K_SPACE:
                show_more = not show_more
            elif event.key == pygame.K_TAB:
                show_one_e_at_a_time = not show_one_e_at_a_time
            elif event.key == pygame.K_RETURN:
                show_envelope_attempt = not show_envelope_attempt
        elif event.type == pygame.MOUSEBUTTONDOWN:
            if event.button == 1:
                left_mouse_held = True
            elif event.button == 2:
                middle_mouse_held = True
            elif event.button == 3:
                right_mouse_held = True
        elif event.type == pygame.MOUSEBUTTONUP:
            if event.button == 1:
                left_mouse_held = False
            elif event.button == 2:
                middle_mouse_held = False
            elif event.button == 3:
                right_mouse_held = False
    
    # Get input in default coords
    mouse_pos = pygame.mouse.get_pos()
    
    if left_mouse_held:
        p_left_mouse = screen_to_def_coords(mouse_pos)
    if middle_mouse_held:
        p_middle_mouse = screen_to_def_coords(mouse_pos)
    if right_mouse_held:
        p_right_mouse = screen_to_def_coords(mouse_pos)
    
    # Map default coordinates to complex numbers
    # unused_1 = def_coords_to_complex(p_middle_mouse)
    # unused_2 = def_coords_to_complex(p_right_mouse)
    
    if show_one_e_at_a_time:
        multiplicative_identity = real_to_complex(1)
        b_prime = def_coords_to_complex(p_right_mouse)
        e_size_complex = def_coords_to_complex((p_left_mouse[0],0))
        e_size = abs(e_size_complex)
        if e_size < 0:
            e_size = 0
        middle_mouse_complex = def_coords_to_complex(p_middle_mouse)
        e_dir = middle_mouse_complex/abs(middle_mouse_complex)
        e = e_size*e_dir
        
        # Do complex maths
        b_prime_size = abs(b_prime)
        e_size_complex = def_coords_to_complex((e_size, 0))
        c_prime_centre = e_size_complex + e_size_complex*(real_to_complex(0) - e_size_complex)
        c_prime_rad = e_size*b_prime_size
        c_bar = (b_prime*e_dir - e_size_complex)
        c_prime = e_size_complex*(b_prime*e_dir - e_size_complex)
        c_bar_offset = e_size_complex + c_bar
        c_prime_offset = e_size_complex + c_prime
        
        
        # Convert complex numbers back into default coordinates
        p_multiplicative_identity = complex_to_def_coords(multiplicative_identity)
        p_b_prime                 = complex_to_def_coords(b_prime)
        p_e                       = complex_to_def_coords(e)
        p_e_size                  = complex_to_def_coords(e_size_complex)
        p_c_prime_centre          = complex_to_def_coords(c_prime_centre)
        p_c_bar                   = complex_to_def_coords(c_bar)
        p_c_prime                 = complex_to_def_coords(c_prime)
        p_c_bar_offset            = complex_to_def_coords(c_bar_offset)
        p_c_prime_offset          = complex_to_def_coords(c_prime_offset)
        
        rad_b_prime_size          = round(def_scale_to_screen_scale(b_prime_size))
        rad_e_size                = round(def_scale_to_screen_scale(e_size))
        rad_c_prime_rad           = round(def_scale_to_screen_scale(c_prime_rad))
        
        # Display it all
        main_surf.fill((0,0,0))
        
        draw_circle(main_surf, GREY, ORIGIN, "")
        
        draw_circle(main_surf, BLUE, p_left_mouse, "LeftBtn = Real(e)", 5, 1)
        if show_more:
            draw_circle(main_surf, BLUE, p_middle_mouse, "MiddleBtn = Dir(e)", 5, 1)
        if show_more:
            draw_circle(main_surf, GREEN, p_right_mouse, "RightBtn", 5, 1)
        else:
            draw_circle(main_surf, GREEN, p_right_mouse, "|RightBtn| = |b'|", 5, 1)
        
        if show_more:
            draw_arrow(main_surf, GREEN, ORIGIN, p_b_prime,             "b'")
        draw_arrow(main_surf, GREY,  ORIGIN, p_multiplicative_identity, "1")
        if show_more:
            draw_arrow(main_surf, BLUE,  ORIGIN, p_e,                   "e")
        draw_arrow(main_surf, BLUE,  ORIGIN, p_e_size,                  "|e|")
        if show_more:
            draw_arrow(main_surf, MAGENTA,  p_e_size, p_c_prime_offset, "c'")
        if show_more:
            draw_arrow(main_surf, DARK_BLUE,  p_e_size, p_c_bar_offset, "c_bar")
        
        draw_circle(main_surf, GREEN, ORIGIN, "", rad_b_prime_size, 1)
        draw_circle(main_surf, BLUE, ORIGIN, "", rad_e_size, 1)
        if show_more:
            draw_circle(main_surf, MAGENTA, p_c_prime_centre, "", rad_c_prime_rad, 1)
        else:
            draw_circle(main_surf, MAGENTA, p_c_prime_centre, "c' on circle", rad_c_prime_rad, 1, (-40,-100))
        
        draw_text(main_surf, GREY,  screen_to_def_coords((10,10)), "Inputs:")
        draw_text(main_surf, GREEN, screen_to_def_coords((10,30)), "b' = {}".format(b_prime))
        draw_text(main_surf, GREEN,  screen_to_def_coords((10,50)), "|b'| = {}".format(b_prime_size))
        draw_text(main_surf, BLUE,  screen_to_def_coords((10,70)), "e = {}".format(e))
        draw_text(main_surf, BLUE,  screen_to_def_coords((10,90)), "|e| = {}".format(e_size))
        draw_text(main_surf, MAGENTA,  screen_to_def_coords((10,110)), "c' = {}".format(c_prime))
        draw_text(main_surf, DARK_BLUE,  screen_to_def_coords((10,130)), "c_bar = {}".format(c_bar))
        draw_text(main_surf, GREY,  screen_to_def_coords((10,150)), "Showing One E at a Time")
        draw_text(main_surf, GREY,  screen_to_def_coords((10,170)), "Press Tab to Show a Range of Es at Once")
        if show_more:
            draw_text(main_surf, GREY,  screen_to_def_coords((10,190)), "Press Space to Show Less")
        else:
            draw_text(main_surf, GREY,  screen_to_def_coords((10,190)), "Press Space to Show More")
        
        pygame.display.flip()
    else:
        # Display for many e
        main_surf.fill((0,0,0))
        
        for e_index in range(0,20):
            e_scale = e_index/2
            multiplicative_identity = real_to_complex(1)
            b_prime = def_coords_to_complex(p_right_mouse)
            e_size_complex = e_scale * multiplicative_identity
            e_size = abs(e_size_complex)
            if e_size < 0:
                e_size = 0
            middle_mouse_complex = def_coords_to_complex(p_middle_mouse)
            if abs(middle_mouse_complex) != 0:
                e_dir = middle_mouse_complex/abs(middle_mouse_complex)
                e = e_size*e_dir
                
                # Do complex maths
                b_prime_size = abs(b_prime)
                e_size_complex = def_coords_to_complex((e_size, 0))
                c_prime_centre_from_e_size = e_size_complex - e_size_complex**2  # e_size_complex + e_size_complex*(real_to_complex(0) - e_size_complex)
                c_prime_centre_from_origin = - e_size_complex**2  # e_size_complex*(real_to_complex(0) - e_size_complex)
                c_prime_rad = e_size*b_prime_size
                c_bar = (b_prime*e_dir - e_size_complex)
                c_prime = e_size_complex*(b_prime*e_dir - e_size_complex)
                c_bar_offset = e_size_complex + c_bar
                c_prime_offset = e_size_complex + c_prime
                
                if show_envelope_attempt and b_prime_size != 0:
                    screen_radius_complex = -def_coords_to_complex(screen_to_def_coords((0,0))).real
                    for envelope_it in range(NO_OF_ENVELOPE_POINTS):
                        envelope_param = envelope_it/(NO_OF_ENVELOPE_POINTS-1)
                        env_y = (1-envelope_param)*(-screen_radius_complex) + envelope_param*(screen_radius_complex)
                        env_x = -env_y**2 / (b_prime_size**2) +  (b_prime_size**2) / 4
                        p_env = complex_to_def_coords(complex(env_x, env_y))
                        draw_circle(main_surf, CYAN, p_env,   "", 5, 1)
                    
                
                # Convert complex numbers back into default coordinates
                p_multiplicative_identity = complex_to_def_coords(multiplicative_identity)
                p_b_prime                 = complex_to_def_coords(b_prime)
                p_e                       = complex_to_def_coords(e)
                p_e_size                  = complex_to_def_coords(e_size_complex)
                p_c_prime_centre_from_e_size = complex_to_def_coords(c_prime_centre_from_e_size)
                p_c_prime_centre_from_origin = complex_to_def_coords(c_prime_centre_from_origin)
                p_c_bar                   = complex_to_def_coords(c_bar)
                p_c_prime                 = complex_to_def_coords(c_prime)
                p_c_bar_offset            = complex_to_def_coords(c_bar_offset)
                p_c_prime_offset          = complex_to_def_coords(c_prime_offset)
                
                rad_b_prime_size          = round(def_scale_to_screen_scale(b_prime_size))
                rad_e_size                = round(def_scale_to_screen_scale(e_size))
                rad_c_prime_rad           = round(def_scale_to_screen_scale(c_prime_rad))
                
                draw_circle(main_surf, GREY, ORIGIN, "")
                
                draw_circle(main_surf, GREEN, p_right_mouse, "|RightBtn| = |b'|", 5, 1)
                
                if show_more:
                    draw_arrow(main_surf, BLUE,  ORIGIN, p_e)
                    draw_arrow(main_surf, BLUE,  ORIGIN, p_e_size)
                    draw_arrow(main_surf, MAGENTA,  p_e_size, p_c_prime_offset, "c'")
                    
                    if rad_c_prime_rad >= 1:
                        draw_circle(main_surf, MAGENTA, p_c_prime_centre_from_e_size, "", rad_c_prime_rad, 1)
                
                if show_more:
                    draw_arrow(main_surf, DARK_MAGENTA,  ORIGIN, p_c_prime, "c'")
                
                if rad_c_prime_rad >= 1:
                    draw_circle(main_surf, DARK_MAGENTA, p_c_prime_centre_from_origin, "", rad_c_prime_rad, 1)
        
        draw_text(main_surf, GREY,  screen_to_def_coords((10,10)), "Inputs:")
        draw_text(main_surf, GREEN, screen_to_def_coords((10,30)), "b' = {}".format(b_prime))
        draw_text(main_surf, GREEN,  screen_to_def_coords((10,50)), "|b'| = {}".format(b_prime_size))
        draw_text(main_surf, GREY,  screen_to_def_coords((10,150)), "Showing a Range of Es at Once")
        draw_text(main_surf, GREY,  screen_to_def_coords((10,170)), "Press Tab to Show One E at a Time")
        if show_more:
            draw_text(main_surf, GREY,  screen_to_def_coords((10,190)), "Press Space to Show Less")
        else:
            draw_text(main_surf, GREY,  screen_to_def_coords((10,190)), "Press Space to Show More")
        if show_envelope_attempt:
            draw_text(main_surf, GREY,  screen_to_def_coords((10,210)), "Press Return to Hide Envelope Attempt")
        else:
            draw_text(main_surf, GREY,  screen_to_def_coords((10,210)), "Press Return to Show Envelope Attempt")
        draw_text(main_surf, MAGENTA,  screen_to_def_coords((10,250)), "Magenta circles are c' = c/a which have solutions for e in (a*e*eConj + b*eConj + c = 0)")
        draw_text(main_surf, GREEN,  screen_to_def_coords((10,270)), "b' = b/a")
        
        draw_circle(main_surf, GREEN, ORIGIN, "", rad_b_prime_size, 1)
        if show_more:
            draw_arrow(main_surf, GREEN, ORIGIN, p_b_prime,                 "b'")
        draw_arrow(main_surf, GREY,  ORIGIN, p_multiplicative_identity, "1")
        if show_more:
            draw_arrow(main_surf, BLUE,  ORIGIN, p_e,                       "e")
        
        pygame.display.flip()

pygame.quit()