// A simple hello world program compatible with C4
// Avoids using loops since they're not fully implemented
#include <stdio.h>

int main() {
    // Print a greeting
    printf("Hello, C4 world!\n");
    
    // Simple variable assignment and arithmetic
    int x = 10;
    int y = 20;
    int sum = x + y;
    
    printf("Sum of %d and %d: %d\n", x, y, sum);
    
    // Demonstrate conditions
    if (sum > 25) {
        printf("Sum is greater than 25\n");
    } else {
        printf("Sum is not greater than 25\n");
    }
    
    // Multiple nested operations
    int result = (x + y) * (y - x) / 2;
    printf("Result of complex calculation: %d\n", result);
    
    return 0;
}