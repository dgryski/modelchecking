/*
 * Based on https://github.com/heidi-ann/runway-model-randcounter/blob/master/counter.js
 * Copyright (c) 2016, Heidi Howard <hh360@cam.ac.uk>
 * This version Copyright (c) 2016, Damian Gryski <damian@gryski.com>
 * All rights reserved.
 * Licensed under the MIT license.
 * For full license text, see LICENSE.md file in the repo root or
 * https://opensource.org/licenses/MIT
 */

"use strict";

let View = function (controller, svg, module) {
    let model = module.env;

    // Update svg to refer to the d3 element
    svg = d3.select(svg);

    let things = ["farmer", "wolf", "goat", "cabbage"];

    let data = things.map(function(x) { return model.vars.get(x) });

    // Create a group for each piece of data
    let counters = svg.selectAll('g')
	    .data(data)
        .enter()
        .append('g');

    // For each counter create a text element and set the text to the value
    counters
	    .append('text')
        .attr('x', function (d, i) { return 10 + i * 25; })
        .attr('y', function (d, i) {
            console.log(d.varianttype.name, i);
            if (d.varianttype.name == "True") {
                return 30
            } else {
                return 10
            }
        })
        .style({
            'text-anchor': 'middle',
            'dominant-baseline': 'central',
            'font-size': 10,
        })
        .text(function (d, i) { console.log("text",things[i]); return things[i][0]; });

    return {
        update: function () {
            var item = 0;
            // On update set the text for each counter to its new value
            counters.selectAll('text')
            .attr('y', function (d) {
                console.log("update", d.varianttype.name);
                if (d.varianttype.name == "True") {
                    return 60
                } else {
                    return 10
                }
            })
            .text(function (d) { console.log("update", item, d); let i=item; item++; return things[i][0]; });
        }
    };

}; // View

module.exports = View;
