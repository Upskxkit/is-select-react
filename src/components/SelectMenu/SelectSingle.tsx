import React, {memo, ReactElement} from "react";
import Paper from "@material-ui/core/Paper";
import "./SelectMenu.scss"
import Typography from "@material-ui/core/Typography";
import {propTypes} from "./propTypes";
import VirtualList from "react-tiny-virtual-list";
import {Item, SingleMenu} from "../../interface";

function SelectSingle({cancelHandler, applyHandler, items, open}: SingleMenu): ReactElement {

  const handleAccept = (item: Item) => () => {
    if (!item.disabled) {
      applyHandler(item);
      cancelHandler();
    }
  };
//TODO DEFINE STYLE FOR TEXT WITH DISABLE
  return (<>
    {open && !!items.length && <Paper className={`popperWrapper popperWrapper`}>
      <VirtualList
        width='100%'
        height={168}
        itemCount={items.length}
        itemSize={28}
        renderItem={({index, style}) => {
          const item = items[index];

          return (
            <div key={index}
                 style={style}
                 className={`option 
                 ${item.checked ? "selected" : ""} 
                 ${item.disabled ? "disabled" : ""} `}
                 onClick={handleAccept(item)}>
              <Typography noWrap aria-disabled className="text" variant="body2">{item.label}</Typography>
            </div>)
        }
        }
      />
    </Paper>}
  </>);
}

SelectSingle.propTypes = propTypes();

export default memo(SelectSingle);
